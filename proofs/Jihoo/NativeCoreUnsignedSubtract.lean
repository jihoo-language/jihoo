import Jihoo.NativeCoreUnsignedCollect
import Jihoo.NativeCoreEffectAnalysis
import Jihoo.NativeCoreTrapAnalysis
import Jihoo.NativeCorePureUnsignedSum
import Jihoo.NativeBindingMachineMutableUnsignedSubtraction

/-! The guarded cancellation pass used by Core.normal for USub. It
collects the two already normalized operands, subtracts the wider literal
sum, and removes only occurrences found by native live identity. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedSubtract

open NativeArena Environment NativeCoreCompare NativeConstantAccumulator
open NativeCoreUnsignedCollect (Collects Pool)
open NativeCoreTrapAnalysis (graphMayTrap)
open NativeCorePureUnsignedSum (keepPrefixes keepPrefixes_refines wrapPrefixes)

structure Residual where
  atoms : List Nat
  constant : BitVec 128
  deriving Repr

/-- A failed guard or a missing atom leaves the unsigned subtraction
neutral. An error retains the first rejecting step. The pending prefixes
from both walks are collected but not reused by this subtraction pass. -/
def cancel (env : Environment) (arena : Arena) (limit depth initial left right : Nat) :
    NativeCoreUnsignedCancellation.Outcome (Option Residual) :=
  match NativeCoreUnsignedCollect.run arena limit depth initial left {} with
  | (.error reason, spent) => (.error reason, spent)
  | (.ok leftPool, spent) =>
      match NativeCoreUnsignedCollect.run arena limit depth spent right {pending := leftPool.pending} with
      | (.error reason, spent) => (.error reason, spent)
      | (.ok rightPool, spent) =>
          if rightPool.constant ≤ leftPool.constant &&
            CoreEffectAnalysis.graphMemoryFree env arena depth left &&
            CoreEffectAnalysis.graphMemoryFree env arena depth right then
            let (result, used) :=
              NativeCoreUnsignedCancellation.run arena limit depth spent leftPool.atoms.toList rightPool.atoms.toList
            (result.map (Option.map fun rest => ⟨rest, leftPool.constant - rightPool.constant⟩), used)
          else (.ok none, spent)

/-- The syntax accounts for the atoms, the collected Strict prefixes, and
the exact mathematical total of all literal occurrences. -/
def Parts (term : Term) (atoms : List Term) (constant : Nat) : Prop :=
  ∃ pending updates visits, Collects term atoms pending updates visits ∧ runNatural updates 0 = some constant

def numerical (value : Shape → Nat) (atoms : List Term) (constant : Nat) : Nat :=
  (atoms.map (value ∘ project)).sum + constant

private theorem collect_parts (represented : Represents arena root term)
    (emptyAtoms : before.atoms.toList = []) (zero : before.constant = 0)
    (collected : NativeCoreUnsignedCollect.run arena limit depth initial root before = (.ok after, spent))
    (ceiling : limit ≤ 1000000) :
    ∃ terms, RepresentsList arena after.atoms.toList terms ∧ Parts term terms after.constant.toNat := by
  obtain ⟨visits, difference, within, ⟨atoms, prefixes, updates, refs, _, trace, refsRep, _, refsEq, _, added⟩⟩ :=
    NativeCoreUnsignedCollect.run_refines represented collected
  have occurrences := trace.literal_budget
  have bounded : literalVisits updates ≤ 1000000 := by omega
  have exactValue := runWord_within_core_steps updates bounded
  rw [zero] at added
  rw [added, Option.map_some] at exactValue
  rw [emptyAtoms, List.nil_append] at refsEq
  exact ⟨atoms, refsEq ▸ refsRep, prefixes, updates, visits, trace, exactValue.symm⟩

private theorem represented_unique (left : RepresentsList arena refs first) (right : RepresentsList arena refs second) :
    first = second := by
  induction refs generalizing first second with
  | nil => cases left; cases right; rfl
  | cons ref rest ih =>
      cases left with
      | cons head tail =>
          cases right with
          | cons other remaining => simp only [Represents.unique head other, ih tail remaining]

private theorem represented_sublist (sub : refs.Sublist pool)
    (held : RepresentsList arena refs atoms) (original : RepresentsList arena pool allAtoms) :
    atoms.Sublist allAtoms := by
  induction sub generalizing atoms allAtoms with
  | slnil => cases held; cases original; exact .slnil
  | cons ref _ ih =>
      cases original with
      | cons head tail => exact .cons _ (ih held tail)
  | cons_cons ref _ ih =>
      cases held with
      | cons current rest =>
          cases original with
          | cons head tail =>
              have same := Represents.unique current head
              cases same
              exact .cons_cons _ (ih rest tail)

structure Agreement (arena : Arena) (first second : Term) (remainder : Residual) : Prop where
  values : ∃ leftAtoms rightAtoms remaining leftConstant rightConstant,
    Parts first leftAtoms leftConstant ∧ Parts second rightAtoms rightConstant ∧
    RepresentsList arena remainder.atoms remaining ∧ remaining.Sublist leftAtoms ∧
    ∀ value, numerical value leftAtoms leftConstant =
      numerical value rightAtoms rightConstant + numerical value remaining remainder.constant.toNat

/-- A successful cancellation has the mathematical subtraction value for
every interpretation of the retained atom shapes. The guard and native
identity account for every removed occurrence and prevent word underflow. -/
theorem cancel_refines (left : Represents arena a first) (right : Represents arena b second)
    (ceiling : limit ≤ 1000000)
    (ran : cancel env arena limit depth initial a b = (.ok (some remaining), spent)) :
    Agreement arena first second remaining := by
  unfold cancel at ran
  rcases collectLeft : NativeCoreUnsignedCollect.run arena limit depth initial a ({} : Pool) with ⟨leftResult, leftSteps⟩
  cases leftResult with
  | error reason =>
      simp only [collectLeft] at ran
      cases ran
  | ok leftPool =>
      simp only [collectLeft] at ran
      rcases collectRight :
          NativeCoreUnsignedCollect.run arena limit depth leftSteps b {pending := leftPool.pending} with
        ⟨rightResult, rightSteps⟩
      cases rightResult with
      | error reason =>
          simp only [collectRight] at ran
          cases ran
      | ok rightPool =>
          simp only [collectRight] at ran
          split at ran
          · rename_i guards
            have noUnderflow : rightPool.constant ≤ leftPool.constant := by
              simp only [Bool.and_eq_true, decide_eq_true_eq] at guards
              first | exact guards.1 | exact guards.1.1
            rcases removed : NativeCoreUnsignedCancellation.run arena limit depth rightSteps
                leftPool.atoms.toList rightPool.atoms.toList with ⟨answer, used⟩
            cases answer with
            | error reason => simp [removed, Except.map] at ran
            | ok found =>
                cases found with
                | none => simp [removed, Except.map] at ran
                | some residual =>
                    simp only [removed, Except.map, Option.map_some, Except.ok.injEq, Option.some.injEq,
                      Prod.mk.injEq] at ran
                    obtain ⟨rfl, rfl⟩ := ran
                    obtain ⟨ls, leftRep, leftParts⟩ := collect_parts left rfl rfl collectLeft ceiling
                    obtain ⟨rs, rightRep, rightParts⟩ := collect_parts right rfl rfl collectRight ceiling
                    constructor
                    have removedValues (value : Shape → Nat) :=
                      NativeCoreUnsignedCancellation.run_value_balance leftRep rightRep removed value
                    obtain ⟨residualTerms, residualRep, _⟩ := removedValues (fun _ => 0)
                    have subset := represented_sublist (NativeCoreUnsignedCancellation.run_sublist removed)
                      residualRep leftRep
                    refine ⟨ls, rs, residualTerms, leftPool.constant.toNat, rightPool.constant.toNat,
                      leftParts, rightParts, residualRep, subset, ?_⟩
                    intro value
                    obtain ⟨terms, matching, balanced⟩ := removedValues value
                    have same := represented_unique matching residualRep
                    subst terms
                    simp only [numerical, BitVec.toNat_sub_of_le noUnderflow]
                    have fits : rightPool.constant.toNat ≤ leftPool.constant.toNat := noUnderflow
                    omega
          · cases ran

inductive Error where
  | collectOrCancel (reason : NativeCoreIdentical.Error)
  | canonical (reason : NativeCoreUnsignedCanonical.Error)
  | graph (reason : NativeCoreGraph.Error)
  deriving DecidableEq, Repr

structure Outcome where
  arena : Arena
  result : Except Error (Option Nat)
  steps : Nat
  deriving Repr

private def trapReferences (env : Environment) (runtime : Bool) (arena : Arena) (depth a b : Nat) :
    List Nat :=
  [b, a].filter (graphMayTrap env runtime arena depth)

/-- This entry starts after Core.normal has normalized the three USub
operands. None requests the original neutral USub rebuild. -/
def run (env : Environment) (runtime : Bool) (arena : Arena) (limit depth initial a b : Nat) : Outcome :=
  match cancel env arena limit depth initial a b with
  | (.error reason, spent) => ⟨arena, .error (.collectOrCancel reason), spent⟩
  | (.ok none, spent) => ⟨arena, .ok none, spent⟩
  | (.ok (some leftover), spent) =>
      let canonical := NativeCoreUnsignedCanonical.run runtime arena leftover.atoms leftover.constant (limit-spent)
      let next := limit - canonical.remaining
      match canonical.result with
      | .error reason => ⟨canonical.arena, .error (.canonical reason), next⟩
      | .ok none => ⟨canonical.arena, .ok none, next⟩
      | .ok (some ref) =>
          let kept := keepPrefixes canonical.arena ref (trapReferences env runtime arena depth a b)
          ⟨kept.arena, (kept.result.map some).mapError .graph, next⟩

private theorem represented_filter (held : RepresentsList arena refs terms) (keep : Nat → Bool) :
    ∃ kept, RepresentsList arena (refs.filter keep) kept ∧ kept.Sublist terms := by
  induction refs generalizing terms with
  | nil => cases held; exact ⟨[], .nil, .slnil⟩
  | cons ref rest ih =>
      cases held with
      | cons head tail =>
          obtain ⟨kept, retained, sublist⟩ := ih tail
          cases decideKeep : keep ref
          · exact ⟨kept, by simpa only [List.filter_cons, decideKeep, Bool.false_eq_true, ite_false] using retained,
              .cons _ sublist⟩
          · exact ⟨_, by simpa only [List.filter_cons, decideKeep, ite_true] using RepresentsList.cons head retained,
              .cons_cons _ sublist⟩

structure Refines (env : Environment) (runtime : Bool) (start finish : Arena) (ctx : Context)
    (first second originalType : Term) (output : Nat) : Prop where
  frame : Prefix start finish
  backward : Backward start → Backward finish
  cancellation : ∃ residual atoms prefixes,
    Agreement start first second residual ∧ RepresentsList start residual.atoms atoms ∧
    prefixes.Sublist [second, first] ∧
    let term := wrapPrefixes (NativeCoreUnsignedCanonical.canonicalTerm runtime atoms residual.constant.toNat) prefixes
    Represents finish output term ∧ LoanTyping.HasType env [] ctx true term originalType

/-- The cancelled branch builds a typed result at the original source type.
Its represented residual satisfies the exact subtraction equation, and the
original potentially trapping operands are wrapped in native order. -/
theorem run_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (left : Represents arena a first) (right : Represents arena b second)
    (checked : LoanTyping.HasType env loans ctx mode (.usub first second proofTerm) originalType)
    (ceiling : limit ≤ 1000000)
    (completed : (run env runtime arena limit depth initial a b).result = .ok (some output)) :
    Refines env runtime arena (run env runtime arena limit depth initial a b).arena ctx first second originalType output := by
  unfold run at completed ⊢
  rcases reduced : cancel env arena limit depth initial a b with ⟨answer, spent⟩
  cases answer with
  | error reason => simp [reduced] at completed
  | ok option =>
      cases option with
      | none => simp [reduced] at completed
      | some residual =>
          simp only [reduced] at completed ⊢
          generalize ordered : NativeCoreUnsignedCanonical.run runtime arena residual.atoms residual.constant
            (limit - spent) = canonical at completed ⊢
          cases emitted : canonical.result with
          | error reason => simp [emitted] at completed
          | ok selected =>
              cases selected with
              | none => simp [emitted] at completed
              | some root =>
                  simp only [emitted] at completed ⊢
                  have canonicalOk :
                      (NativeCoreUnsignedCanonical.run runtime arena residual.atoms residual.constant
                        (limit - spent)).result = .ok (some root) := by rw [ordered, emitted]
                  have semantic := cancel_refines left right ceiling reduced
                  obtain ⟨_, _, atoms, _, _, leftParts, _, represented, retains, _⟩ := semantic.values
                  obtain ⟨_, _, _, traced, _⟩ := leftParts
                  obtain ⟨leftTyped, rightTyped, evidence⟩ := checked.usub_inputs
                  have principal : LoanTyping.HasType env loans ctx mode (.usub first second proofTerm) .u64 :=
                    .usub leftTyped rightTyped evidence
                  have original := principal.unique wellFormed checked
                  obtain ⟨_, typedAtoms⟩ := NativeCoreUnsignedSoundness.typed_trace traced left.wellFormed
                    (leftTyped.ghost [])
                  have built := NativeCoreUnsignedCanonical.run_refines represented canonicalOk
                  rw [ordered] at built
                  obtain ⟨frame, result, backward⟩ := built
                  have resultTyped := (NativeCoreUnsignedCanonical.canonicalTerm_typed
                    (runtime := runtime) (constant := residual.constant.toNat)
                    (fun atom member => typedAtoms.atomsTyped atom (retains.subset member))).convert original
                  have operands : RepresentsList arena [b, a] [second, first] := .cons right (.cons left .nil)
                  obtain ⟨prefixes, prefixRep, prefixSublist⟩ :=
                    represented_filter operands (graphMayTrap env runtime arena depth)
                  have prefixTypes : ∀ term ∈ prefixes, ∃ type, LoanTyping.HasType env [] ctx true term type := by
                    intro term member
                    have original := prefixSublist.subset member
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at original
                    rcases original with rfl | rfl
                    · exact ⟨.u64, rightTyped.ghost []⟩
                    · exact ⟨.u64, leftTyped.ghost []⟩
                  cases wrapped : (keepPrefixes canonical.arena root
                      (trapReferences env runtime arena depth a b)).result with
                  | error reason => simp [wrapped, Except.map, Except.mapError] at completed
                  | ok selectedRoot =>
                      simp only [wrapped, Except.map, Except.mapError, Except.ok.injEq, Option.some.injEq] at completed
                      subst selectedRoot
                      obtain ⟨nextFrame, outputRep, _, outputTyped, nextBack⟩ :=
                        keepPrefixes_refines (prefixRep.frame frame) result resultTyped prefixTypes wrapped
                      exact ⟨frame.trans nextFrame, fun previous => nextBack (backward previous),
                        ⟨residual, atoms, prefixes, semantic, represented, prefixSublist, outputRep, outputTyped⟩⟩

/-- Cancelling (k + 1) - 1 returns k and retains evaluation of the original
potentially overflowing addition, without a second read of the subtrahend. -/
theorem cancellation_retains_addition_trap :
    let arena : Arena := #[.var 0, .node (.natural 1) [], .node .uadd [0, 1]]
    run Environment.empty true arena 5 3 0 2 1 =
      ⟨arena.push (.node .strict [2, 0]), .ok (some 3), 5⟩ := by
  cbv

theorem fallback_preserves_arena (fallback : (run env runtime arena limit depth initial a b).result = .ok none) :
    (run env runtime arena limit depth initial a b).arena = arena := by
  unfold run at fallback ⊢
  rcases attempted : cancel env arena limit depth initial a b with ⟨answer, spent⟩
  cases answer with
  | error reason => simp [attempted] at fallback
  | ok answer =>
      cases answer with
      | none => rfl
      | some captured =>
          simp only [attempted] at fallback ⊢
          generalize ordered : NativeCoreUnsignedCanonical.run runtime arena captured.atoms captured.constant
              (limit-spent) = canonical at fallback ⊢
          cases emitted : canonical.result with
          | error reason => simp [emitted] at fallback
          | ok result =>
              cases result with
              | none =>
                  rw [← ordered] at emitted
                  have preserved := NativeCoreUnsignedCanonical.run_fallback emitted
                  rw [ordered] at preserved
                  rw [preserved]
              | some ref =>
                  cases kept : (keepPrefixes canonical.arena ref
                      (trapReferences env runtime arena depth a b)).result <;>
                    simp [emitted, kept, Except.map, Except.mapError] at fallback

private def neutral (arena : Arena) (original a b proofRef : Nat) : NativeCoreNaturalSum.Outcome :=
  let row := Node.node .usub [a, b, proofRef]
  if arena[original]? = some row then ⟨arena, .ok original⟩
  else match NativeCoreGraph.addNode arena row with
    | .error reason => ⟨arena, .error reason⟩
    | .ok (after, ref) => ⟨after, .ok ref⟩

structure RootOutcome where
  arena : Arena
  result : Except Error Nat
  steps : Nat
  deriving Repr

def runAfterOperands (env : Environment) (runtime : Bool) (arena : Arena)
    (limit depth initial original a b proofRef : Nat) : RootOutcome :=
  let folded := run env runtime arena limit depth initial a b
  match folded.result with
  | .error reason => ⟨folded.arena, .error reason, folded.steps⟩
  | .ok (some ref) => ⟨folded.arena, .ok ref, folded.steps⟩
  | .ok none =>
      let rebuilt := neutral folded.arena original a b proofRef
      ⟨rebuilt.arena, rebuilt.result.mapError .graph, folded.steps⟩

private theorem represented_index (held : Represents arena ref term) : ref < arena.size := by
  cases held with
  | var row | node row => exact (Array.getElem?_eq_some_iff.mp row).1

private theorem neutral_refines (left : Represents arena a first) (right : Represents arena b second)
    (proof : Represents arena proofRef evidence) (built : (neutral arena original a b proofRef).result = .ok output) :
    let next := (neutral arena original a b proofRef).arena
    Prefix arena next ∧ Represents next output (.usub first second evidence) ∧ (Backward arena → Backward next) := by
  by_cases reused : arena[original]? = some (.node .usub [a, b, proofRef])
  · simp only [neutral, reused, ite_true] at built ⊢
    cases built
    exact ⟨.refl _, .node reused rfl (.cons left (.cons right (.cons proof .nil))), fun before => before⟩
  · simp only [neutral, reused, ite_false] at built ⊢
    cases added : NativeCoreGraph.addNode arena (.node .usub [a, b, proofRef]) with
    | error reason => simp [added] at built
    | ok appended =>
      obtain ⟨next, ref⟩ := appended
      simp only [added] at built ⊢
      cases built
      obtain ⟨frame, index, _, _, _, row⟩ := NativeCoreGraph.addNode_commits added
      refine ⟨frame, .node row rfl (.cons (left.frame frame) (.cons (right.frame frame)
        (.cons (proof.frame frame) .nil))), ?_⟩
      intro backwards
      apply NativeCoreGraph.addNode_preserves_backward backwards added
      rw [index]
      intro ref
      simp only [Node.references, List.mem_cons, List.mem_nil_iff, or_false]
      rintro (rfl | rfl | rfl)
      · exact represented_index left
      · exact represented_index right
      · exact represented_index proof

/-- After all three operands are normalized, both the contracted and
neutral rebuild branches preserve the original checked type. In the
neutral branch the normalized proof reference is retained. -/
theorem runAfterOperands_refines (wellFormed : UnifiedProgram.EnvWellFormed env)
    (left : Represents arena a first) (right : Represents arena b second)
    (proof : Represents arena proofRef evidence)
    (checked : LoanTyping.HasType env loans ctx mode (.usub first second evidence) originalType)
    (ceiling : limit ≤ 1000000)
    (computed : (runAfterOperands env runtime arena limit depth initial original a b proofRef).result = .ok output) :
    let after := (runAfterOperands env runtime arena limit depth initial original a b proofRef).arena
    ∃ term, Prefix arena after ∧ Represents after output term ∧
      LoanTyping.HasType env [] ctx true term originalType ∧ (Backward arena → Backward after) ∧
      ((run env runtime arena limit depth initial a b).result = .ok none → term = .usub first second evidence) := by
  unfold runAfterOperands at computed ⊢
  cases folded : (run env runtime arena limit depth initial a b).result with
  | error reason => simp [folded] at computed
  | ok result =>
      cases result with
      | none =>
          have unchanged := fallback_preserves_arena folded
          simp only [folded, unchanged] at computed ⊢
          cases rebuilt : (neutral arena original a b proofRef).result with
          | error reason => simp [rebuilt, Except.mapError] at computed
          | ok selected =>
              simp only [rebuilt, Except.mapError, Except.ok.injEq] at computed
              subst selected
              obtain ⟨frame, represented, backward⟩ := neutral_refines left right proof rebuilt
              exact ⟨_, frame, represented, checked.ghost [], backward, fun _ => rfl⟩
      | some selected =>
          simp only [folded, Except.ok.injEq] at computed ⊢
          subst selected
          obtain ⟨frame, backward, _, _, _, _, _, _, represented, typed⟩ :=
            run_refines wellFormed left right checked ceiling folded
          exact ⟨_, frame, represented, typed, backward, by intro impossible; cases impossible⟩

end Jihoo.NativeKernel.NativeCoreUnsignedSubtract
