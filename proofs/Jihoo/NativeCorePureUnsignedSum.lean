import Jihoo.NativeCoreUnsignedSoundness

/-! Core.sum after operand normalization, when the collected atom pool has
no root USub to cancel. The actual Strict-wrapping loop retains each
collected prefix in the live arena. -/
namespace Jihoo.NativeKernel.NativeCorePureUnsignedSum

open NativeArena Environment NativeCoreGraph
open NativeCoreUnsignedCollect (runOperands)
open NativeCoreUnsignedSoundness (collect_operands_and_emit_typed)

inductive Error where
  | collect (reason : NativeCoreIdentical.Error)
  | cancellation
  | canonical (reason : NativeCoreUnsignedCanonical.Error)
  | graph (reason : NativeCoreGraph.Error)
  deriving Repr, DecidableEq

structure Outcome where
  arena : Arena
  result : Except Error Nat
  steps : Nat
  deriving Repr

private def hasSubtraction (arena : Arena) (ref : Nat) : Bool :=
  match arena[ref]? with
  | some (.node .usub _) => true
  | _ => false

def keepPrefixes (arena : Arena) (result : Nat) : List Nat → NativeCoreNaturalSum.Outcome
  | [] => ⟨arena, .ok result⟩
  | first :: rest =>
      match addNode arena (.node .strict [first, result]) with
      | .error reason => ⟨arena, .error reason⟩
      | .ok (next, wrapped) => keepPrefixes next wrapped rest

/-- This entry starts after the two calls to Core.normal. Each completed
collection and comparison spends from the original remaining budget. -/
def run (arena : Arena) (limit depth initial left right : Nat) : Outcome :=
  match runOperands arena limit depth initial left right with
  | (.error reason, spent) => ⟨arena, .error (.collect reason), spent⟩
  | (.ok collected, spent) =>
      if collected.atoms.any (hasSubtraction arena) then ⟨arena, .error .cancellation, spent⟩
      else
        let canonical := NativeCoreUnsignedCanonical.run false arena collected.atoms.toList collected.constant (limit-spent)
        let after := limit - canonical.remaining
        match canonical.result with
        | .error reason => ⟨canonical.arena, .error (.canonical reason), after⟩
        | .ok none => ⟨canonical.arena, .error .cancellation, after⟩
        | .ok (some result) =>
            let wrapped := keepPrefixes canonical.arena result collected.pending.toList
            ⟨wrapped.arena, wrapped.result.mapError .graph, after⟩

private theorem in_arena (represented : Represents arena ref term) : ref < arena.size := by
  cases represented with
  | var row | node row => exact (Array.getElem?_eq_some_iff.mp row).1

private theorem wrap_refines (first : Represents arena x effect) (result : Represents arena y value)
    (added : addNode arena (.node .strict [x, y]) = .ok (next, wrapped)) :
    Prefix arena next ∧ Represents next wrapped (.strict effect value) ∧ (Backward arena → Backward next) := by
  obtain ⟨frame, index, _, _, _, row⟩ := addNode_commits added
  refine ⟨frame, .node row rfl (.cons (first.frame frame) (.cons (result.frame frame) .nil)), ?_⟩
  intro backward
  apply addNode_preserves_backward backward added
  rw [index]
  intro child
  simp only [Node.references, List.mem_cons, List.mem_nil_iff, or_false]
  rintro (rfl | rfl)
  · exact in_arena first
  · exact in_arena result

def wrapPrefixes (result : Term) (prefixes : List Term) : Term :=
  prefixes.foldl (fun value first => .strict first value) result

theorem keepPrefixes_refines
    (effects : RepresentsList arena refs terms)
    (value : Represents arena root result)
    (typed : LoanTyping.HasType env [] ctx true result originalType)
    (prefixes : ∀ effect ∈ terms, ∃ type, LoanTyping.HasType env [] ctx true effect type)
    (built : (keepPrefixes arena root refs).result = .ok output) :
    let after := (keepPrefixes arena root refs).arena
    let term := wrapPrefixes result terms
    Prefix arena after ∧ Represents after output term ∧ RawValue.Conv env result term ∧
      LoanTyping.HasType env [] ctx true term originalType ∧ (Backward arena → Backward after) := by
  induction refs generalizing arena root result terms with
  | nil =>
      cases effects
      cases built
      exact ⟨.refl _, value, .refl _, typed, fun before => before⟩
  | cons first refs ih =>
      cases effects with
      | cons head tail =>
          unfold keepPrefixes at built ⊢
          cases added : addNode arena (.node .strict [first, root]) with
          | error reason => simp [added] at built
          | ok node =>
              obtain ⟨next, reference⟩ := node
              simp only [added] at built ⊢
              obtain ⟨frame, represented, backward⟩ := wrap_refines head value added
              obtain ⟨_, firstTyped⟩ := prefixes _ List.mem_cons_self
              obtain ⟨nextFrame, resultRep, converted, nextTyped, nextBackward⟩ :=
                ih (tail.frame frame) represented (.strict firstTyped typed)
                  (fun effect member => prefixes effect (List.mem_cons_of_mem _ member)) built
              exact ⟨frame.trans nextFrame, resultRep, (RawValue.Conv.strict _ _).symm.trans converted,
                nextTyped, fun before => nextBackward (backward before)⟩

/-- The completed ghost sum represents a term convertible to the original
operand sum and preserves the exact checked type. Backwardness and every
earlier reference survive the complete append sequence. -/
theorem run_refines (left : Represents arena a first) (right : Represents arena b second)
    (checked : LoanTyping.HasType env loans ctx mode (.uadd first second) originalType)
    (limitBound : limit ≤ 1000000)
    (completed : (run arena limit depth initial a b).result = .ok output) :
    let after := (run arena limit depth initial a b).arena
    ∃ term, Prefix arena after ∧ Represents after output term ∧ RawValue.Conv env (.uadd first second) term ∧
      LoanTyping.HasType env [] ctx true term originalType ∧ (Backward arena → Backward after) := by
  unfold run at completed ⊢
  rcases walked : runOperands arena limit depth initial a b with ⟨answer, spent⟩
  cases answer with
  | error reason => simp [walked] at completed
  | ok seen =>
      simp only [walked] at completed ⊢
      by_cases cancels : seen.atoms.any (hasSubtraction arena) = true
      · simp [cancels] at completed
      · simp only [cancels, Bool.false_eq_true, ite_false] at completed ⊢
        generalize ordered :
          NativeCoreUnsignedCanonical.run false arena seen.atoms.toList seen.constant (limit-spent) =
            canonical at completed ⊢
        cases emitted : canonical.result with
        | error reason => simp [emitted] at completed
        | ok selected =>
            cases selected with
            | none => simp [emitted] at completed
            | some root =>
                simp only [emitted] at completed ⊢
                have selected :
                    (NativeCoreUnsignedCanonical.run false arena seen.atoms.toList seen.constant (limit-spent)).result =
                      .ok (some root) := by rw [ordered, emitted]
                have typed := collect_operands_and_emit_typed left right checked limitBound walked selected
                rw [ordered] at typed
                obtain ⟨bare, prefixes, represented, effects, same, bareTyped, prefixesTyped⟩ := typed.result
                cases wrapped : (keepPrefixes canonical.arena root seen.pending.toList).result with
                | error reason => simp [wrapped, Except.mapError] at completed
                | ok final =>
                    simp only [wrapped, Except.mapError, Except.ok.injEq] at completed
                    subst final
                    obtain ⟨frame, resultRep, converted, finalTyped, backward⟩ :=
                      keepPrefixes_refines (effects.frame typed.frame) represented bareTyped prefixesTyped wrapped
                    exact ⟨_, typed.frame.trans frame, resultRep, same.trans converted, finalTyped,
                      fun before => backward (typed.backward before)⟩

end Jihoo.NativeKernel.NativeCorePureUnsignedSum
