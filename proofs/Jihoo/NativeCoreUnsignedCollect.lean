import Jihoo.NativeCoreUnsignedCancellation
import Jihoo.NativeCoreNaturalSum

/-! Core.collect flattens unsigned additions, retaining Strict prefixes in
evaluation order and charging a fresh tick for each visited occurrence. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedCollect

open NativeArena NativeConstantAccumulator
open NativeCoreUnsignedCancellation (Outcome tick)

inductive View (α : Type) where
  | sum (left right : α)
  | strict (prefixTerm result : α)
  | literal (word : UInt64)
  | atom

def view (op : Op) (children : List α) : View α :=
  match op, children with
  | .uadd, [left, right] => .sum left right
  | .strict, [first, result] => .strict first result
  | .natural value, _ => .literal (UInt64.ofNat value)
  | _, _ => .atom

def nodeView : Node → View Nat
  | .var _ => .atom
  | .node op refs => view op refs

def termView : Term → View Term
  | .var _ => .atom
  | .node op terms => view op terms

structure Pool where
  atoms : Array Nat := #[]
  pending : Array Nat := #[]
  constant : BitVec 128 := 0
  deriving Repr, Inhabited

def run (arena : Arena) (limit : Nat) : Nat → Nat → Nat → Pool → Outcome Pool
  | 0, steps, root, _ =>
      let charged := tick arena limit 0 steps root
      match charged.1 with
      | .error reason => (.error reason, charged.2)
      | .ok _ => (.error (.depthLimit root), charged.2)
  | depth + 1, steps, root, before =>
      match tick arena limit (depth + 1) steps root with
      | (.error reason, spent) => (.error reason, spent)
      | (.ok (), spent) =>
          match arena[root]?.map nodeView with
          | none => (.error (.invalidReference root), spent)
          | some (.sum left right) =>
              match run arena limit depth spent left before with
              | (.error reason, spent) => (.error reason, spent)
              | (.ok afterLeft, spent) => run arena limit depth spent right afterLeft
          | some (.strict first result) =>
              run arena limit depth spent result {before with pending := before.pending.push first}
          | some (.literal word) =>
              (.ok {before with constant := before.constant + BitVec.ofNat 128 word.toNat}, spent)
          | some .atom => (.ok {before with atoms := before.atoms.push root}, spent)

/-- The independent traversal of unfolded syntax, with recorded literal
updates, retained atoms, and prefixes that must still be evaluated. -/
inductive Collects : Term → List Term → List Term → List Update → Nat → Prop where
  | sum : termView term = .sum left right →
      Collects left ats pts xs leftVisits → Collects right bts qts ys rightVisits →
      Collects term (ats ++ bts) (pts ++ qts) (xs ++ ys) (leftVisits + rightVisits + 1)
  | strict : termView term = .strict first result → Collects result ats pts xs visits →
      Collects term ats (first :: pts) xs (visits + 1)
  | literal : termView term = .literal word → Collects term [] [] [.literal word] 1
  | atom : termView term = .atom → Collects term [term] [] [] 1

private inductive ViewMeaning (arena : Arena) : View Nat → View Term → Prop where
  | sum : Represents arena x a → Represents arena y b → ViewMeaning arena (.sum x y) (.sum a b)
  | strict : Represents arena x a → Represents arena y b → ViewMeaning arena (.strict x y) (.strict a b)
  | literal : ViewMeaning arena (.literal word) (.literal word)
  | atom : ViewMeaning arena .atom .atom

private theorem view_meaning (op : Op) (children : RepresentsList arena refs terms)
    (arity : refs.length = op.arity) : ViewMeaning arena (view op refs) (view op terms) := by
  cases op
  all_goals try exact .atom
  case uadd =>
    cases children with
    | nil => cases arity
    | cons left rest =>
        cases rest with
        | nil => cases arity
        | cons right rest =>
            cases rest with
            | nil => exact .sum left right
            | cons => cases arity
  case strict =>
    cases children with
    | nil => cases arity
    | cons first rest =>
        cases rest with
        | nil => cases arity
        | cons result rest =>
            cases rest with
            | nil => exact .strict first result
            | cons => cases arity
  case natural => exact .literal

private theorem node_view (represented : Represents arena root term) :
    ∃ observed, arena[root]?.map nodeView = some observed ∧ ViewMeaning arena observed (termView term) := by
  cases represented with
  | var read => exact ⟨.atom, by simp [read, nodeView], .atom⟩
  | node read arity children => exact ⟨_, by simp [read, nodeView], view_meaning _ children arity⟩

private theorem append_rep (left : RepresentsList arena xs leftTerms) (right : RepresentsList arena ys rightTerms) :
    RepresentsList arena (xs ++ ys) (leftTerms ++ rightTerms) := by
  induction left using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => exact right
  | cons head _ _ rest => exact .cons head rest

private theorem runWord_append (first second : List Update) (constant : BitVec 128) :
    runWord (first ++ second) constant = (runWord first constant).bind (runWord second) := by
  induction first generalizing constant with
  | nil => rfl
  | cons update rest ih =>
      cases update with
      | literal word => exact ih _
      | cancel word =>
          simp only [List.cons_append, runWord]
          split
          · exact ih _
          · rfl

private theorem tick_success (ran : tick arena limit depth initial root = (.ok (), spent)) :
    spent = initial + 1 ∧ spent ≤ limit := by
  by_cases over : limit < initial + 1
  · simp [tick, over] at ran
  by_cases zero : depth = 0
  · simp [tick, over, zero] at ran
  by_cases invalid : arena.size ≤ root
  · simp [tick, over, zero, invalid] at ran
  · simp only [tick, over, zero, invalid, ite_false, Prod.mk.injEq] at ran
    obtain ⟨_, rfl⟩ := ran
    exact ⟨rfl, Nat.le_of_not_gt over⟩

private theorem at_zero (ran : run arena limit 0 initial root before = (.ok after, spent)) : False := by
  by_cases over : limit < initial + 1 <;> simp [run, tick, over] at ran

structure Agreement (arena : Arena) (term : Term) (before after : Pool) (visits : Nat) : Prop where
  trace : ∃ ats pts updates xs ys,
    Collects term ats pts updates visits ∧
    RepresentsList arena xs ats ∧ RepresentsList arena ys pts ∧
    after.atoms.toList = before.atoms.toList ++ xs ∧
    after.pending.toList = before.pending.toList ++ ys ∧
    runWord updates before.constant = some after.constant

/-- A complete live-arena traversal exposes exactly the accumulated terms
and the literal updates. The visit count is the actual counter difference. -/
theorem run_refines (represented : Represents arena root term)
    (ran : run arena limit depth initial root before = (.ok after, spent)) :
    ∃ visits, spent = initial + visits ∧ spent ≤ limit ∧ Agreement arena term before after visits := by
  induction depth generalizing root term initial before after spent with
  | zero => exact (at_zero ran).elim
  | succ depth ih =>
      obtain ⟨observed, read, meaning⟩ := node_view represented
      rcases charged : tick arena limit (depth + 1) initial root with ⟨answer, afterTick⟩
      cases answer with
      | error reason => simp [run, charged] at ran
      | ok tickValue =>
          cases tickValue
          have ticked := tick_success charged
          simp only [run, charged, read] at ran
          generalize termKind : termView term = kind at meaning
          cases meaning with
          | @sum x a y b leftRep rightRep =>
              rcases visited : run arena limit depth afterTick x before with ⟨result, afterLeft⟩
              cases result with
              | error reason => simp [visited] at ran
              | ok middle =>
                  simp only [visited] at ran
                  obtain ⟨leftVisits, leftSpent, _, ⟨leftAtoms, leftPending, leftUpdates, leftRefs, leftPrefixes,
                    leftTrace, leftAtomsRep, leftPendingRep, leftAtomsEq, leftPendingEq, leftSum⟩⟩ := ih leftRep visited
                  obtain ⟨rightVisits, rightSpent, room, ⟨rightAtoms, rightPending, rightUpdates, rightRefs,
                    rightPrefixes, rightTrace, rightAtomsRep, rightPendingRep, rightAtomsEq, rightPendingEq,
                    rightSum⟩⟩ := ih rightRep ran
                  refine ⟨leftVisits + rightVisits + 1, by omega, room, ?_⟩
                  exact ⟨_, _, _, _, _, .sum termKind leftTrace rightTrace, append_rep leftAtomsRep rightAtomsRep,
                    append_rep leftPendingRep rightPendingRep, by rw [rightAtomsEq, leftAtomsEq, List.append_assoc],
                    by rw [rightPendingEq, leftPendingEq, List.append_assoc],
                    by rw [runWord_append, leftSum]; exact rightSum⟩
          | @strict x a y b firstRep resultRep =>
              obtain ⟨visits, resultSpent, room, ⟨atoms, pending, updates, refs, prefixes, trace, atomsRep,
                pendingRep, atomsEq, pendingEq, sum⟩⟩ := ih resultRep ran
              refine ⟨visits + 1, by omega, room, ?_⟩
              exact ⟨_, _, _, _, _, .strict termKind trace, atomsRep, .cons firstRep pendingRep, atomsEq,
                by simpa [List.append_assoc] using pendingEq, sum⟩
          | literal =>
              simp only [Prod.mk.injEq, Except.ok.injEq] at ran
              obtain ⟨rfl, rfl⟩ := ran
              exact ⟨1, ticked.1, ticked.2, ⟨[], [], _, [], [], .literal termKind, .nil, .nil,
                by simp, by simp, rfl⟩⟩
          | atom =>
              simp only [Prod.mk.injEq, Except.ok.injEq] at ran
              obtain ⟨rfl, rfl⟩ := ran
              exact ⟨1, ticked.1, ticked.2, ⟨[term], [], [], [root], [], .atom termKind,
                .cons represented .nil, .nil, by simp, by simp, rfl⟩⟩

private theorem literalVisits_append (first second : List Update) :
    literalVisits (first ++ second) = literalVisits first + literalVisits second := by
  induction first with
  | nil => simp [literalVisits]
  | cons update rest ih =>
      cases update <;> simp only [List.cons_append, literalVisits, ih] <;> omega

theorem Collects.literal_budget (collected : Collects term atoms pending updates visits) :
    literalVisits updates ≤ visits := by
  induction collected with
  | sum _ _ _ left right => rw [literalVisits_append]; omega
  | strict _ _ result => omega
  | literal _ => simp [literalVisits]
  | atom _ => simp [literalVisits]

/-- Starting from an empty accumulator, the production tick ceiling
guarantees exact U128 accumulation even when many visits share one node. -/
theorem run_exact_constant (limitBound : limit ≤ 1000000)
    (represented : Represents arena root term)
    (ran : run arena limit depth initial root {} = (.ok after, spent)) :
    ∃ atoms pending updates visits,
      Collects term atoms pending updates visits ∧ literalVisits updates ≤ 1000000 ∧
      runWord updates 0 = some after.constant ∧ runNatural updates 0 = some after.constant.toNat := by
  obtain ⟨visits, counted, within, ⟨atoms, pending, updates, _, _, collected, _, _, _, _, summed⟩⟩ :=
    run_refines represented ran
  have literalBound := collected.literal_budget
  have ceiling : literalVisits updates ≤ 1000000 := by omega
  have exactSum := runWord_within_core_steps updates ceiling
  change runWord updates 0 = some after.constant at summed
  rw [summed, Option.map_some] at exactSum
  exact ⟨atoms, pending, updates, visits, collected, ceiling, summed, exactSum.symm⟩

/-- The emitted constant from a successful collection run preserves the
exact unsigned value and fits within the balanced tree depth bound. -/
theorem run_emit_constant (limitBound : limit ≤ 1000000)
    (represented : Represents arena root term)
    (collected : run arena limit depth initial root {} = (.ok after, spent))
    (emitted : (NativeCoreNaturalSum.run after.constant.toNat arena).result = .ok constantRef) :
    ∃ constantTerm,
      Represents (NativeCoreNaturalSum.run after.constant.toNat arena).arena constantRef constantTerm ∧
      EnvironmentDelta.NumeralForward.Represents constantTerm after.constant.toNat ∧
      Environment.LoanTyping.HasType env loans ctx mode constantTerm .u64 ∧
      Conversion.treeDepth constantTerm ≤ 21 := by
  obtain ⟨_, _, updates, _, _, bound, accumulated, _⟩ := run_exact_constant limitBound represented collected
  have meaning := (NativeCoreNaturalSum.run_refines _ _ emitted).1
  have ⟨numeric, typed⟩ := naturalSum_correct after.constant.toNat
    (env := env) (loans := loans) (ctx := ctx) (mode := mode)
  exact ⟨_, meaning, numeric, typed, collected_naturalSum_depth (updates := updates) bound accumulated⟩

/-- Strict's prefix is retained without collecting its arithmetic, while
both references to the shared natural leaf are visited and accumulated. -/
theorem shared_literal_and_pending_example :
    let arena : Arena := #[.node (.natural 7) [], .node (.natural 99) [], .node .strict [1, 0],
      .node .uadd [2, 0]]
    run arena 4 3 0 3 {} = (.ok {pending := #[1], constant := 14}, 4) := rfl

end Jihoo.NativeKernel.NativeCoreUnsignedCollect
