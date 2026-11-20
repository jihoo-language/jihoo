import Jihoo.NativeCoreUnsignedSumRounds

/-! The Core.sum branch after both operands have normalized. The original
counter is shared by collecting, removing matching occurrences, and
canonical ordering. Appending nodes preserves earlier arena references. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedSum

open NativeArena Environment NativeCoreGraph
open NativeCoreUnsignedCollect (Pool Collects)
open NativeCoreUnsignedSumRounds (rounds)
open NativeCorePureUnsignedSum (keepPrefixes keepPrefixes_refines wrapPrefixes)
open NativeCoreTrapAnalysis (graphMayTrap)

inductive Error where
  | traversal (reason : NativeCoreIdentical.Error)
  | order
  | graph (reason : NativeCoreGraph.Error)
  deriving Repr, DecidableEq

structure Outcome where
  arena : Arena
  result : Except Error Nat
  /-- The ordering model reports failure without the exact rejecting tick. -/
  steps : Option Nat
  deriving Repr

private def unchangedSum (arena : Arena) (left right steps : Nat) : Outcome :=
  match addNode arena (.node .uadd [left, right]) with
  | .error reason => ⟨arena, .error (.graph reason), some steps⟩
  | .ok (after, root) => ⟨after, .ok root, some steps⟩

def finish (runtime : Bool) (arena : Arena) (limit spent left right : Nat) (pool : Pool) : Outcome :=
  let ordered := NativeCoreUnsignedCanonical.run runtime arena pool.atoms.toList pool.constant (limit-spent)
  let steps := limit - ordered.remaining
  match ordered.result with
  | .error .order => ⟨ordered.arena, .error .order, none⟩
  | .error (.graph reason) => ⟨ordered.arena, .error (.graph reason), some steps⟩
  | .ok none => unchangedSum ordered.arena left right steps
  | .ok (some root) =>
      let kept := keepPrefixes ordered.arena root pool.pending.toList
      ⟨kept.arena, kept.result.mapError .graph, some steps⟩

def run (env : Environment) (runtime : Bool) (arena : Arena) (limit depth initial left right : Nat) : Outcome :=
  match NativeCoreUnsignedCollect.runOperands arena limit depth initial left right with
  | (.error reason, spent) => ⟨arena, .error (.traversal reason), some spent⟩
  | (.ok collected, spent) =>
      match rounds env runtime arena limit depth collected spent with
      | (.error reason, spent) => ⟨arena, .error (.traversal reason), some spent⟩
      | (.ok (after, _), spent) => finish runtime arena limit spent left right after

/-- The wide runtime constant takes the original UAdd path before ordering
and never appends a balanced constant tree or any Strict wrappers. -/
theorem finish_runtime_overflow (wide : 2^64 ≤ pool.constant.toNat) (inBudget : spent ≤ limit) :
    finish true arena limit spent left right pool =
      match addNode arena (.node .uadd [left, right]) with
      | .error reason => ⟨arena, .error (.graph reason), some spent⟩
      | .ok (after, root) => ⟨after, .ok root, some spent⟩ := by
  change finish true arena limit spent left right pool = unchangedSum arena left right spent
  have fallback : NativeCoreUnsignedCanonical.run true arena pool.atoms.toList pool.constant (limit-spent) =
      ⟨arena, .ok none, limit-spent⟩ := by simp [NativeCoreUnsignedCanonical.run, wide]
  simp only [finish, fallback, Nat.sub_sub_self inBudget]

private def TypedRef (arena : Arena) (predicate : Term → Prop) (reference : Nat) : Prop :=
  ∃ term, Represents arena reference term ∧ predicate term

private theorem typedRefs (represented : RepresentsList arena refs terms) (typed : ∀ term ∈ terms, predicate term) :
    ∀ ref ∈ refs, TypedRef arena predicate ref := by
  induction refs generalizing terms with
  | nil => simp
  | cons ref rest ih =>
      cases represented with
      | cons head tail =>
          intro next member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_, head, typed _ List.mem_cons_self⟩
          · exact ih tail (fun t h => typed t (List.mem_cons_of_mem _ h)) _ member

private theorem typedTerms (typed : ∀ ref ∈ refs, TypedRef arena predicate ref) :
    ∃ terms, RepresentsList arena refs terms ∧ ∀ t ∈ terms, predicate t := by
  induction refs with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons ref rest ih =>
      obtain ⟨head, represented, typedHead⟩ := typed ref List.mem_cons_self
      obtain ⟨tail, representedTail, typedTail⟩ :=
        ih (fun next member => typed next (List.mem_cons_of_mem _ member))
      refine ⟨head :: tail, .cons represented representedTail, ?_⟩
      intro t member
      rcases List.mem_cons.mp member with rfl | member
      · exact typedHead
      · exact typedTail _ member

private abbrev TypedAtom (env : Environment) (ctx : Context) (arena : Arena) : Nat → Prop :=
  TypedRef arena (fun term => LoanTyping.HasType env [] ctx true term .u64)

private abbrev TypedPrefix (env : Environment) (ctx : Context) (arena : Arena) : Nat → Prop :=
  TypedRef arena (fun term => ∃ type, LoanTyping.HasType env [] ctx true term type)

private structure TypedPool (env : Environment) (ctx : Context) (arena : Arena) (pool : Pool) : Prop where
  atoms : ∀ ref ∈ pool.atoms.toList, TypedAtom env ctx arena ref
  pending : ∀ ref ∈ pool.pending.toList, TypedPrefix env ctx arena ref

private theorem collect_typed (rootTyped : TypedAtom env ctx arena root) (beforeTyped : TypedPool env ctx arena before)
    (collected : NativeCoreUnsignedCollect.run arena limit depth initial root before = (.ok after, spent)) :
    TypedPool env ctx arena after := by
  obtain ⟨term, represented, checked⟩ := rootTyped
  obtain ⟨_, _, _, ⟨_, _, _, _, _, trace, refsRep, prefixRep, atomsEq, pendingEq, _⟩⟩ :=
    NativeCoreUnsignedCollect.run_refines represented collected
  obtain ⟨_, typing⟩ := NativeCoreUnsignedSoundness.typed_trace trace represented.wellFormed checked
  refine ⟨?_, ?_⟩
  · rw [atomsEq]
    intro ref member
    rcases List.mem_append.mp member with member | member
    · exact beforeTyped.atoms ref member
    · exact typedRefs refsRep typing.atomsTyped ref member
  · rw [pendingEq]
    intro ref member
    rcases List.mem_append.mp member with member | member
    · exact beforeTyped.pending ref member
    · exact typedRefs prefixRep typing.pendingTyped ref member

private theorem operands_typed (left : Represents arena a first) (right : Represents arena b second)
    (checked : LoanTyping.HasType env loans ctx mode (.uadd first second) originalType)
    (collected : NativeCoreUnsignedCollect.runOperands arena limit depth initial a b = (.ok pool, spent)) :
    TypedPool env ctx arena pool := by
  unfold NativeCoreUnsignedCollect.runOperands at collected
  rcases firstRun : NativeCoreUnsignedCollect.run arena limit depth initial a ({} : Pool) with ⟨answer, checkedAt⟩
  cases answer with
  | error reason =>
      simp only [firstRun] at collected
      cases collected
  | ok leftPool =>
      simp only [firstRun] at collected
      obtain ⟨leftTyped, rightTyped, _⟩ := checked.uadd_inputs
      have empty : TypedPool env ctx arena ({} : Pool) := ⟨by simp, by simp⟩
      have firstTyped := collect_typed ⟨first, left, leftTyped.ghost []⟩ empty firstRun
      exact collect_typed ⟨second, right, rightTyped.ghost []⟩ firstTyped collected

private theorem subtraction_inputs
    (typed : TypedAtom env ctx arena ref)
    (read : arena[ref]? = some (.node .usub [numerator, denominator, evidence])) :
    TypedAtom env ctx arena numerator ∧ TypedAtom env ctx arena denominator := by
  obtain ⟨term, represented, checked⟩ := typed
  cases represented with
  | var lookup =>
      rw [read] at lookup
      cases lookup
  | node lookup _ children =>
      rw [read] at lookup
      cases lookup
      cases children with
      | cons first rest =>
          cases rest with
          | cons second rest =>
              cases rest with
              | cons proof rest =>
                  cases rest
                  obtain ⟨left, right, _⟩ := checked.usub_inputs
                  exact ⟨⟨_, first, left⟩, ⟨_, second, right⟩⟩

private theorem attempt_typed (before : TypedPool env ctx arena pool)
    (others : ∀ ref ∈ otherRefs, TypedAtom env ctx arena ref)
    (left : TypedAtom env ctx arena numerator) (right : TypedAtom env ctx arena denominator)
    (ran : NativeCoreUnsignedSumRounds.attempt env runtime arena limit depth
      otherRefs numerator denominator pool initial = (.ok (some after), spent)) :
    TypedPool env ctx arena after := by
  unfold NativeCoreUnsignedSumRounds.attempt at ran
  rcases collected : NativeCoreUnsignedCollect.run arena limit depth initial denominator ({} : Pool) with
    ⟨answer, collectedAt⟩
  cases answer with
  | error reason =>
      simp only [collected] at ran
      cases ran
  | ok minus =>
      simp only [collected] at ran
      split at ran
      · cases ran
      · rcases removed : NativeCoreUnsignedCancellation.run arena limit depth collectedAt
          otherRefs minus.atoms.toList with ⟨answer, removedAt⟩
        cases answer with
        | error reason =>
            simp only [removed] at ran
            cases ran
        | ok result =>
            cases result with
            | none =>
                simp only [removed] at ran
                cases ran
            | some remaining =>
                simp only [removed] at ran
                let start : Pool := ⟨remaining.toArray,
                  if graphMayTrap env runtime arena depth denominator then pool.pending.push denominator else pool.pending,
                  pool.constant - minus.constant⟩
                change (let result := NativeCoreUnsignedCollect.run arena limit depth removedAt numerator start
                  (result.1.map some, result.2)) = (.ok (some after), spent) at ran
                rcases replenished : NativeCoreUnsignedCollect.run arena limit depth removedAt numerator start with
                  ⟨answer, replenishedAt⟩
                cases answer with
                | error reason =>
                    simp only [replenished, Except.map] at ran
                    cases ran
                | ok final =>
                    simp only [replenished, Except.map, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at ran
                    obtain ⟨rfl, rfl⟩ := ran
                    have sublist := NativeCoreUnsignedCancellation.run_sublist removed
                    have startTyped : TypedPool env ctx arena start := by
                      refine ⟨?_, ?_⟩
                      · intro ref member
                        have kept : ref ∈ remaining := by simpa [start] using member
                        exact others _ (sublist.subset kept)
                      · intro ref member
                        by_cases preserve : graphMayTrap env runtime arena depth denominator = true
                        · have added : ref ∈ pool.pending.toList ++ [denominator] := by
                            simpa only [start, preserve, ite_true, Array.toList_push] using member
                          rcases List.mem_append.mp added with old | new
                          · exact before.pending ref old
                          · obtain rfl := List.mem_singleton.mp new
                            obtain ⟨term, reference, typed⟩ := right
                            exact ⟨term, reference, _, typed⟩
                        · exact before.pending ref (by simpa [start, preserve] using member)
                    exact collect_typed left startTyped replenished

private theorem scan_typed (before : TypedPool env ctx arena pool)
    (inputs : ∀ ref ∈ earlier.reverse ++ refs, TypedAtom env ctx arena ref)
    (ran : NativeCoreUnsignedSumRounds.scan env runtime arena limit depth pool earlier refs initial =
      (.ok (some after), spent)) : TypedPool env ctx arena after := by
  induction refs generalizing earlier initial with
  | nil => cases ran
  | cons ref rest ih =>
      have carried (probe : Nat) (member : probe ∈ (ref :: earlier).reverse ++ rest) :
          TypedAtom env ctx arena probe :=
        inputs probe (by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using member)
      simp only [NativeCoreUnsignedSumRounds.scan] at ran
      split at ran
      · rename_i numerator denominator evidence read
        rcases attempted : NativeCoreUnsignedSumRounds.attempt env runtime arena limit depth
          (earlier.reverse ++ rest) numerator denominator pool initial with ⟨answer, checkedAt⟩
        cases answer with
        | error reason =>
            simp only [attempted] at ran
            cases ran
        | ok found =>
            cases found with
            | none =>
                simp only [attempted] at ran
                exact ih carried ran
            | some result =>
                simp only [attempted, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at ran
                obtain ⟨rfl, rfl⟩ := ran
                have candidate := inputs ref (List.mem_append_right _ List.mem_cons_self)
                obtain ⟨left, right⟩ := subtraction_inputs candidate read
                refine attempt_typed before (fun probe member => inputs probe ?_) left right attempted
                rcases List.mem_append.mp member with member | member
                · exact List.mem_append_left _ member
                · exact List.mem_append_right _ (List.mem_cons_of_mem _ member)
      · exact ih carried ran

private theorem loop_typed (typed : TypedPool env ctx arena pool)
    (ran : NativeCoreUnsignedSumRounds.runRounds env runtime arena limit depth n pool initial =
      (.ok (after, count), spent)) : TypedPool env ctx arena after := by
  induction n generalizing pool after count initial spent with
  | zero =>
      cases ran
      exact typed
  | succ n ih =>
      simp only [NativeCoreUnsignedSumRounds.runRounds] at ran
      rcases inspected : NativeCoreUnsignedSumRounds.scan env runtime arena limit depth pool
          [] pool.atoms.toList initial with ⟨answer, checkedAt⟩
      cases answer with
      | error reason =>
          simp only [inspected] at ran
          cases ran
      | ok found =>
          cases found with
          | none =>
              simp only [inspected, Prod.mk.injEq, Except.ok.injEq] at ran
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ran
              exact typed
          | some next =>
              simp only [inspected] at ran
              have nextTyped := scan_typed typed (by simpa using typed.atoms) inspected
              rcases rest : NativeCoreUnsignedSumRounds.runRounds env runtime arena limit depth n
                  next checkedAt with ⟨answer, ticks⟩
              cases answer with
              | error reason =>
                  simp only [rest, Except.map] at ran
                  cases ran
              | ok remaining =>
                  obtain ⟨last, priorCount⟩ := remaining
                  simp only [rest, Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ran
                  exact ih nextTyped rest

private theorem rounds_typed (typed : TypedPool env ctx arena pool)
    (ran : rounds env runtime arena limit depth pool initial = (.ok (after, count), spent)) :
    TypedPool env ctx arena after := by
  unfold rounds at ran
  split at ran
  · exact loop_typed typed ran
  · cases ran
    exact typed

structure Refines (env : Environment) (ctx : Context) (before after : Arena)
    (output : Nat) (originalType : Term) : Prop where
  frame : Prefix before after
  backward : Backward before → Backward after
  typed : ∃ term, Represents after output term ∧ LoanTyping.HasType env [] ctx true term originalType

private theorem in_arena (held : Represents arena ref term) : ref < arena.size := by
  cases held with
  | var row | node row => exact (Array.getElem?_eq_some_iff.mp row).1

private theorem unchangedSum_refines (left : Represents arena a first) (right : Represents arena b second)
    (checked : LoanTyping.HasType env loans ctx mode (.uadd first second) originalType)
    (built : (unchangedSum arena a b spent).result = .ok output) :
    Refines env ctx arena (unchangedSum arena a b spent).arena output originalType := by
  unfold unchangedSum at built ⊢
  cases added : addNode arena (.node .uadd [a, b]) with
  | error reason => simp [added] at built
  | ok appended =>
      obtain ⟨next, ref⟩ := appended
      simp only [added, Except.ok.injEq] at built
      subst ref
      obtain ⟨frame, exactIndex, _, _, _, row⟩ := addNode_commits added
      refine ⟨frame, ?_, .uadd first second, .node row rfl (.cons (left.frame frame)
        (.cons (right.frame frame) .nil)), checked.ghost []⟩
      intro backward
      apply addNode_preserves_backward backward added
      rw [exactIndex]
      intro child member
      simp only [Node.references, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl
      · exact in_arena left
      · exact in_arena right

private theorem finish_refines (left : Represents arena a first) (right : Represents arena b second)
    (checked : LoanTyping.HasType env loans ctx mode (.uadd first second) originalType)
    (typed : TypedPool env ctx arena pool)
    (built : (finish runtime arena limit spent a b pool).result = .ok output) :
    Refines env ctx arena (finish runtime arena limit spent a b pool).arena output originalType := by
  unfold finish at built ⊢
  generalize ordered : NativeCoreUnsignedCanonical.run runtime arena pool.atoms.toList pool.constant
    (limit-spent) = canonical at built ⊢
  cases emitted : canonical.result with
  | error reason =>
      cases reason <;> simp [emitted] at built
  | ok selected =>
      cases selected with
      | none =>
          have neutral : (NativeCoreUnsignedCanonical.run runtime arena pool.atoms.toList pool.constant
            (limit-spent)).result = .ok none := by rw [ordered, emitted]
          have same := NativeCoreUnsignedCanonical.run_fallback neutral
          rw [ordered] at same
          simp only [same] at built ⊢
          exact unchangedSum_refines left right checked built
      | some root =>
          simp only [emitted] at built ⊢
          have canonicalResult : (NativeCoreUnsignedCanonical.run runtime arena pool.atoms.toList pool.constant
            (limit-spent)).result = .ok (some root) := by rw [ordered, emitted]
          obtain ⟨atoms, atomsRep, atomsTyped⟩ := typedTerms typed.atoms
          obtain ⟨prefixes, prefixesRep, prefixesTyped⟩ := typedTerms typed.pending
          obtain ⟨_, _, resultType⟩ := checked.uadd_inputs
          have canonicalCorrect := NativeCoreUnsignedCanonical.run_refines atomsRep canonicalResult
          rw [ordered] at canonicalCorrect
          obtain ⟨frame, represented, backward⟩ := canonicalCorrect
          have canonicalTyped :=
            (NativeCoreUnsignedCanonical.canonicalTerm_typed (runtime := runtime)
              (constant := pool.constant.toNat) atomsTyped).convert resultType
          cases kept : (keepPrefixes canonical.arena root pool.pending.toList).result with
          | error reason => simp [kept, Except.mapError] at built
          | ok ref =>
              simp only [kept, Except.mapError, Except.ok.injEq] at built
              subst ref
              obtain ⟨suffix, result, _, typing, backwardSuffix⟩ :=
                keepPrefixes_refines (prefixesRep.frame frame) represented canonicalTyped prefixesTyped kept
              exact ⟨frame.trans suffix, fun old => backwardSuffix (backward old), _, result, typing⟩

/-- Every successful post-operand UAdd follows the native control flow and
retains its original checked type in the enlarged arena. The same proof
covers each cancellation round and the wide runtime fallback. -/
theorem run_refines (left : Represents arena a first) (right : Represents arena b second)
    (checked : LoanTyping.HasType env loans ctx mode (.uadd first second) originalType)
    (built : (run env runtime arena limit depth initial a b).result = .ok output) :
    Refines env ctx arena (run env runtime arena limit depth initial a b).arena output originalType := by
  unfold run at built ⊢
  rcases collected : NativeCoreUnsignedCollect.runOperands arena limit depth initial a b with ⟨answer, collectedAt⟩
  cases answer with
  | error reason =>
      simp only [collected] at built
      cases built
  | ok input =>
      simp only [collected] at built ⊢
      rcases scanned : rounds env runtime arena limit depth input collectedAt with ⟨answer, spent⟩
      cases answer with
      | error reason =>
          simp only [scanned] at built
          cases built
      | ok result =>
          obtain ⟨pool, count⟩ := result
          simp only [scanned] at built ⊢
          exact finish_refines left right checked (rounds_typed (operands_typed left right checked collected) scanned)
            built

/-- The same two operands use the same counter in both modes. Runtime
keeps its original addition, while ghost computation shares the two
equal halves of the balanced constant. -/
theorem wide_sum_uses_original_runtime_operands :
    let arena : Arena := #[.node (.natural (2^64-1)) [], .node (.natural 1) []]
    run Environment.empty true arena 2 4 0 0 1 =
      ⟨arena.push (.node .uadd [0, 1]), .ok 2, some 2⟩ ∧
    run Environment.empty false arena 2 4 0 0 1 =
      ⟨(arena.push (.node (.natural (2^63)) [])).push (.node .uadd [2, 2]), .ok 3, some 2⟩ := by
  constructor <;> cbv

end Jihoo.NativeKernel.NativeCoreUnsignedSum
