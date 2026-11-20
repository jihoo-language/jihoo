import Jihoo.NativeCoreUnsignedSubtract

/-! Core.sum scans the collected pool for the first subtraction whose
denominator can be paid by the other occurrences. Each successful rewrite
restarts the scan with the replacement pool. Collection and live identity
share the original checking counter. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedSumRounds

open NativeArena Environment NativeConstantAccumulator
open NativeCoreUnsignedCollect (Pool Collects)
open NativeCoreUnsignedCancellation (Outcome)
open NativeCoreTrapAnalysis (graphMayTrap)
open NativeCoreUnsignedSubtract (Parts numerical)

private abbrev maxLiteral : Nat := 2^64 - 1

def attempt (env : Environment) (runtime : Bool) (arena : Arena) (limit depth : Nat)
    (others : List Nat) (numerator denominator : Nat) (pool : Pool) (initial : Nat) :
    Outcome (Option Pool) :=
  match NativeCoreUnsignedCollect.run arena limit depth initial denominator {} with
  | (.error reason, spent) => (.error reason, spent)
  | (.ok minus, spent) =>
      if pool.constant < minus.constant || !minus.pending.isEmpty then (.ok none, spent)
      else
        match NativeCoreUnsignedCancellation.run arena limit depth spent others minus.atoms.toList with
        | (.error reason, spent) => (.error reason, spent)
        | (.ok none, spent) => (.ok none, spent)
        | (.ok (some rest), spent) =>
            let pending := if graphMayTrap env runtime arena depth denominator then
                pool.pending.push denominator else pool.pending
            let start : Pool := ⟨rest.toArray, pending, pool.constant - minus.constant⟩
            let completed := NativeCoreUnsignedCollect.run arena limit depth spent numerator start
            (completed.1.map some, completed.2)

/-- The earlier occurrences are accumulated in reverse order for scanning.
On a candidate, the actual pool supplied to without keeps their original
order and excludes exactly the candidate's occurrence. -/
def scan (env : Environment) (runtime : Bool) (arena : Arena) (limit depth : Nat) (pool : Pool) :
    List Nat → List Nat → Nat → Outcome (Option Pool)
  | _, [], initial => (.ok none, initial)
  | earlier, ref :: later, initial =>
      match arena[ref]? with
      | some (.node .usub [numerator, denominator, _]) =>
          match attempt env runtime arena limit depth (earlier.reverse ++ later) numerator denominator pool initial with
          | (.ok none, spent) => scan env runtime arena limit depth pool (ref :: earlier) later spent
          | result => result
      | _ => scan env runtime arena limit depth pool (ref :: earlier) later initial

/-- The extra count is the number of successful rewrites. The native loop
also runs one unsuccessful scan when it reaches a fixed point before 64
rewrites. -/
def runRounds (env : Environment) (runtime : Bool) (arena : Arena) (limit depth : Nat) :
    Nat → Pool → Nat → Outcome (Pool × Nat)
  | 0, pool, initial => (.ok (pool, 0), initial)
  | rounds+1, pool, initial =>
      match scan env runtime arena limit depth pool [] pool.atoms.toList initial with
      | (.error reason, spent) => (.error reason, spent)
      | (.ok none, spent) => (.ok (pool, 0), spent)
      | (.ok (some next), spent) =>
          let result := runRounds env runtime arena limit depth rounds next spent
          (result.1.map (fun (final, count) => (final, count + 1)), result.2)

def rounds (env : Environment) (runtime : Bool) (arena : Arena) (limit depth : Nat)
    (pool : Pool) (initial : Nat) : Outcome (Pool × Nat) :=
  if pool.atoms.toList.all (CoreEffectAnalysis.graphMemoryFree env arena depth) then
    runRounds env runtime arena limit depth 64 pool initial
  else (.ok (pool, 0), initial)

theorem rounds_blocked (effectful : ref ∈ pool.atoms.toList)
    (effect : CoreEffectAnalysis.graphMemoryFree env arena depth ref = false) :
    rounds env runtime arena limit depth pool initial = (.ok (pool, 0), initial) := by
  unfold rounds
  by_cases accepted : pool.atoms.toList.all (CoreEffectAnalysis.graphMemoryFree env arena depth) = true
  · rw [List.all_eq_true] at accepted
    have contradiction := (accepted ref effectful).symm.trans effect
    cases contradiction
  · simp [accepted]

private theorem repeat_count (ran : runRounds env runtime arena limit depth n pool initial = (.ok (after, count), spent)) :
    count ≤ n := by
  induction n generalizing pool initial after count spent with
  | zero => simp [runRounds] at ran; omega
  | succ n ih =>
      simp only [runRounds] at ran
      rcases inspected : scan env runtime arena limit depth pool [] pool.atoms.toList initial with ⟨answer, steps⟩
      cases answer with
      | error reason => simp [inspected] at ran
      | ok found =>
          cases found with
          | none => simp [inspected] at ran; omega
          | some changed =>
              simp only [inspected] at ran
              rcases rest : runRounds env runtime arena limit depth n changed steps with ⟨answer, ticks⟩
              cases answer with
              | error reason => simp [rest, Except.map] at ran
              | ok remaining =>
                  obtain ⟨last, priorCount⟩ := remaining
                  have bounded := ih rest
                  simp only [rest, Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
                  omega

theorem rounds_count (ran : rounds env runtime arena limit depth pool initial = (.ok (after, count), spent)) :
    count ≤ 64 := by
  unfold rounds at ran
  split at ran
  · exact repeat_count ran
  · cases ran; omega

private def Within (initial limit : Nat) (outcome : Outcome α) : Prop :=
  initial ≤ outcome.2 ∧ outcome.2 ≤ limit + 1 ∧
    ∀ result, outcome.1 = .ok result → outcome.2 ≤ limit

private theorem Within.rebase (before : initial ≤ middle) (within : Within middle limit result) :
    Within initial limit result :=
  ⟨Nat.le_trans before within.1, within.2⟩

private theorem Within.map {result : Outcome α} (within : Within initial limit result) (f : α → β) :
    Within initial limit (result.1.map f, result.2) := by
  obtain ⟨answer, spent⟩ := result
  refine ⟨within.1, within.2.1, ?_⟩
  intro _ finished
  cases answer with
  | error => cases finished
  | ok answer => exact within.2.2 answer rfl

private theorem within_ok {result : α} (room : initial ≤ limit) :
    Within initial limit (.ok result, initial) :=
  ⟨Nat.le_refl _, Nat.le_trans room (Nat.le_succ _), fun _ _ => room⟩

private theorem within_error {α : Type} (monotone : initial ≤ spent) (always : spent ≤ limit + 1) :
    Within (α := α) initial limit (.error reason, spent) :=
  ⟨monotone, always, by intro _ failed; cases failed⟩

private theorem collect_bounds (room : initial ≤ limit) :
    Within initial limit (NativeCoreUnsignedCollect.run arena limit depth initial root pool) := by
  induction depth generalizing initial root pool with
  | zero =>
      by_cases over : limit < initial + 1
      · simp only [NativeCoreUnsignedCollect.run, NativeCoreUnsignedCancellation.tick, over, ite_true]
        exact within_error (Nat.le_succ _) (Nat.succ_le_succ room)
      · simp only [NativeCoreUnsignedCollect.run, NativeCoreUnsignedCancellation.tick, over, ite_false, ite_true]
        exact within_error (Nat.le_succ _) (Nat.succ_le_succ room)
  | succ depth ih =>
      by_cases over : limit < initial + 1
      · simp only [NativeCoreUnsignedCollect.run, NativeCoreUnsignedCancellation.tick, over, ite_true]
        exact within_error (Nat.le_succ _) (Nat.succ_le_succ room)
      have next : initial+1 ≤ limit := Nat.le_of_not_gt over
      by_cases invalid : arena.size ≤ root
      · simp only [NativeCoreUnsignedCollect.run, NativeCoreUnsignedCancellation.tick,
          over, Nat.succ_ne_zero, ite_false, invalid, ite_true]
        exact within_error (Nat.le_succ _) (Nat.le_trans next (Nat.le_succ _))
      · simp only [NativeCoreUnsignedCollect.run, NativeCoreUnsignedCancellation.tick,
          over, Nat.succ_ne_zero, invalid, ite_false]
        split
        · exact within_error (Nat.le_succ _) (Nat.le_trans next (Nat.le_succ _))
        · rename_i left right _
          have leftBounds : Within (initial+1) limit
              (NativeCoreUnsignedCollect.run arena limit depth (initial+1) left pool) := ih next
          rcases walked : NativeCoreUnsignedCollect.run arena limit depth (initial+1) left pool with ⟨answer, spent⟩
          rw [walked] at leftBounds
          cases answer with
          | error reason => exact within_error (Nat.le_trans (Nat.le_succ _) leftBounds.1) leftBounds.2.1
          | ok after =>
              exact Within.rebase (Nat.le_trans (Nat.le_succ _) leftBounds.1) (ih (leftBounds.2.2 after rfl))
        · exact Within.rebase (Nat.le_succ _) (ih next)
        · exact Within.rebase (Nat.le_succ _) (within_ok next)
        · exact Within.rebase (Nat.le_succ _) (within_ok next)

private theorem attempt_bounds (room : initial ≤ limit) :
    Within initial limit (attempt env runtime arena limit depth others numerator denominator pool initial) := by
  unfold attempt
  have denominatorBounds : Within initial limit
      (NativeCoreUnsignedCollect.run arena limit depth initial denominator ({} : Pool)) := collect_bounds room
  rcases collected : NativeCoreUnsignedCollect.run arena limit depth initial denominator ({} : Pool) with
    ⟨answer, spent⟩
  rw [collected] at denominatorBounds
  cases answer with
  | error reason => exact within_error denominatorBounds.1 denominatorBounds.2.1
  | ok minus =>
      have paid := denominatorBounds.2.2 minus rfl
      dsimp only []
      split
      · exact Within.rebase denominatorBounds.1 (within_ok paid)
      · have removed : Within spent limit
            (NativeCoreUnsignedCancellation.run arena limit depth spent others minus.atoms.toList) :=
          NativeCoreUnsignedCancellation.run_step_bounds paid
        rcases matched : NativeCoreUnsignedCancellation.run arena limit depth spent others minus.atoms.toList with
          ⟨answer, checked⟩
        rw [matched] at removed
        apply Within.rebase denominatorBounds.1
        cases answer with
        | error reason => exact within_error removed.1 removed.2.1
        | ok found =>
            have within := removed.2.2 found rfl
            cases found with
            | none => exact Within.rebase removed.1 (within_ok within)
            | some rest => exact Within.rebase removed.1 (Within.map (collect_bounds within) _)

private theorem scan_bounds (room : initial ≤ limit) :
    Within initial limit (scan env runtime arena limit depth pool earlier refs initial) := by
  induction refs generalizing earlier initial with
  | nil => exact within_ok room
  | cons ref rest ih =>
      simp only [scan]
      split
      · rename_i numerator denominator evidence _
        have bounded : Within initial limit
            (attempt env runtime arena limit depth (earlier.reverse ++ rest) numerator denominator pool initial) :=
          attempt_bounds room
        rcases called :
            attempt env runtime arena limit depth (earlier.reverse ++ rest) numerator denominator pool initial with
          ⟨answer, spent⟩
        rw [called] at bounded
        cases answer with
        | error reason => exact within_error bounded.1 bounded.2.1
        | ok found =>
            cases found with
            | none => exact Within.rebase bounded.1 (ih (bounded.2.2 none rfl))
            | some after => exact bounded
      · exact ih room

private theorem repeat_bounds (room : initial ≤ limit) :
    Within initial limit (runRounds env runtime arena limit depth n pool initial) := by
  induction n generalizing pool initial with
  | zero => exact within_ok room
  | succ n ih =>
      simp only [runRounds]
      have bounded : Within initial limit
          (scan env runtime arena limit depth pool [] pool.atoms.toList initial) := scan_bounds room
      rcases inspected : scan env runtime arena limit depth pool [] pool.atoms.toList initial with ⟨answer, spent⟩
      rw [inspected] at bounded
      cases answer with
      | error reason => exact within_error bounded.1 bounded.2.1
      | ok found =>
          have within := bounded.2.2 found rfl
          cases found with
          | none => exact Within.rebase bounded.1 (within_ok within)
          | some after => exact Within.rebase bounded.1 (Within.map (ih within) _)

/-- The effect guard and loop bookkeeping consume no ticks. Even an
unsuccessful scan retains the charges for collection, matching and shifted
entries. Only the first failing tick can exceed the checking budget. -/
theorem rounds_step_bounds (room : initial ≤ limit) :
    let result := rounds env runtime arena limit depth pool initial
    initial ≤ result.2 ∧ result.2 ≤ limit + 1 ∧
      ∀ output, result.1 = .ok output → result.2 ≤ limit := by
  change Within initial limit (rounds env runtime arena limit depth pool initial)
  unfold rounds
  split
  · exact repeat_bounds room
  · exact within_ok room

private def literalValue : Update → Nat
  | .literal word => word.toNat
  | .cancel _ => 0

private theorem runNatural_append (first second : List Update) (initial : Nat) :
    runNatural (first ++ second) initial = (runNatural first initial).bind (runNatural second) := by
  induction first generalizing initial with
  | nil => rfl
  | cons step rest ih =>
      cases step with
      | literal => exact ih _
      | cancel =>
          simp only [List.cons_append, runNatural]
          split
          · exact ih _
          · rfl

private theorem collect_literals (collected : Collects source atoms pending updates visits) (initial : Nat) :
    runNatural updates initial = some (initial + (updates.map literalValue).sum) := by
  induction collected generalizing initial with
  | sum _ _ _ left right =>
      rw [runNatural_append, left]
      simp only [Option.bind_some, right, List.map_append, List.sum_append, Nat.add_assoc]
  | strict _ _ result => exact result _
  | literal => rfl
  | atom => simp [runNatural]

private theorem collect_accurate (represented : Represents arena root term)
    (accumulated : before.constant.toNat ≤ initial * maxLiteral) (ceiling : limit ≤ 1000000)
    (ran : NativeCoreUnsignedCollect.run arena limit depth initial root before = (.ok after, spent)) :
    ∃ newAtoms newPending atomRefs pendingRefs amount,
      RepresentsList arena atomRefs newAtoms ∧ RepresentsList arena pendingRefs newPending ∧
      after.atoms.toList = before.atoms.toList ++ atomRefs ∧
      after.pending.toList = before.pending.toList ++ pendingRefs ∧
      Parts term newAtoms amount ∧
      after.constant.toNat = before.constant.toNat + amount ∧
      after.constant.toNat ≤ spent * maxLiteral := by
  obtain ⟨visits, counted, room, ⟨atoms, pending, updates, refs, prefixes, collected,
    atomsRep, pendingRep, atomsEq, pendingEq, word⟩⟩ := NativeCoreUnsignedCollect.run_refines represented ran
  let amount := (updates.map literalValue).sum
  have occurrences := collected.literal_budget
  have bound : before.constant.toNat + literalVisits updates * maxLiteral ≤ spent * maxLiteral := by
    rw [counted, Nat.add_mul]
    exact Nat.add_le_add accumulated (Nat.mul_le_mul_right _ occurrences)
  have capacity : spent * maxLiteral < 2^128 :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_trans room ceiling)) (by decide)
  have exactWord := runWord_exact updates before.constant (Nat.lt_of_le_of_lt bound capacity)
  rw [word, Option.map_some, collect_literals collected] at exactWord
  have sum := Option.some.inj exactWord
  have natural : runNatural updates before.constant.toNat = some after.constant.toNat :=
    (collect_literals collected _).trans exactWord.symm
  refine ⟨atoms, pending, refs, prefixes, amount, atomsRep, pendingRep, atomsEq, pendingEq,
    ⟨pending, updates, visits, collected, ?_⟩, sum, ?_⟩
  · simpa only [Nat.zero_add] using collect_literals collected 0
  · exact Nat.le_trans (runNatural_bound natural) bound

private theorem represented_append (first : RepresentsList arena xs terms)
    (last : RepresentsList arena ys more) :
    RepresentsList arena (xs ++ ys) (terms ++ more) := by
  induction first using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => exact last
  | cons head _ _ tail => exact .cons head tail

private theorem represented_unique (first : RepresentsList arena refs terms)
    (second : RepresentsList arena refs more) : terms = more := by
  induction refs generalizing terms more with
  | nil => cases first; cases second; rfl
  | cons ref rest ih =>
      cases first with
      | cons head tail =>
          cases second with
          | cons same other => rw [Represents.unique head same, ih tail other]

structure Rewrite (arena : Arena) (pool after : Pool)
    (left right : Term) (others : List Term) : Prop where
  values : ∃ addends subtrahends resultAtoms leftConstant rightConstant,
    Parts left addends leftConstant ∧ Parts right subtrahends rightConstant ∧
    RepresentsList arena after.atoms.toList resultAtoms ∧
    ∀ value,
      numerical value resultAtoms after.constant.toNat + numerical value subtrahends rightConstant =
        numerical value others pool.constant.toNat + numerical value addends leftConstant

/-- Every accepted candidate removes exactly the required denominator
occurrences, using native comparison shapes for equality. Recollecting the
numerator from the guarded difference is exact in U128. -/
theorem attempt_refines (left : Represents arena numerator a) (right : Represents arena denominator b)
    (others : RepresentsList arena otherRefs otherTerms)
    (accumulated : pool.constant.toNat ≤ initial * maxLiteral) (ceiling : limit ≤ 1000000)
    (ran : attempt env runtime arena limit depth otherRefs numerator denominator pool initial =
      (.ok (some after), spent)) :
    Rewrite arena pool after a b otherTerms ∧ after.constant.toNat ≤ spent * maxLiteral := by
  unfold attempt at ran
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
      · rename_i valid
        have canSubtract : minus.constant ≤ pool.constant := by
          have notLess : ¬pool.constant < minus.constant := by
            intro less
            exact valid (by simp [less])
          exact Nat.le_of_not_gt notLess
        obtain ⟨subtrahends, _, subRefs, _, rightConstant, subRep, _, refsEq, _, subParts, subConstant, _⟩ :=
          collect_accurate right (by simp) ceiling collected
        have subAmount : minus.constant.toNat = rightConstant := by simpa using subConstant
        have requested : RepresentsList arena minus.atoms.toList subtrahends := by
          have outputRefs : minus.atoms.toList = subRefs := by simpa using refsEq
          exact outputRefs ▸ subRep
        rcases removed : NativeCoreUnsignedCancellation.run arena limit depth collectedAt
            otherRefs minus.atoms.toList with ⟨answer, removedAt⟩
        cases answer with
        | error reason => simp [removed] at ran
        | ok result =>
            cases result with
            | none => simp [removed] at ran
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
                | error reason => simp [replenished, Except.map] at ran
                | ok final =>
                    simp only [replenished, Except.map, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at ran
                    obtain ⟨rfl, rfl⟩ := ran
                    obtain ⟨_, collectedCount, within, _⟩ := NativeCoreUnsignedCollect.run_refines right collected
                    have afterScan := (NativeCoreUnsignedCancellation.run_step_bounds
                      (arena := arena) (depth := depth) (pool := otherRefs) (items := minus.atoms.toList)
                      within).1
                    rw [removed] at afterScan
                    have earlier : initial ≤ removedAt := by omega
                    have reduced : start.constant.toNat = pool.constant.toNat - minus.constant.toNat :=
                      BitVec.toNat_sub_of_le canSubtract
                    have startBound : start.constant.toNat ≤ removedAt * maxLiteral := by
                      rw [reduced]
                      exact Nat.le_trans (Nat.sub_le _ _)
                        (Nat.le_trans accumulated (Nat.mul_le_mul_right _ earlier))
                    obtain ⟨addends, _, addRefs, _, leftConstant, addRep, _, outputEq, _, addParts,
                      addConstant, bound⟩ := collect_accurate left startBound ceiling replenished
                    obtain ⟨rest, restRep, _⟩ :=
                      NativeCoreUnsignedCancellation.run_value_balance others requested removed (fun _ => 0)
                    refine ⟨⟨addends, subtrahends, rest ++ addends, leftConstant, rightConstant,
                      addParts, subParts, ?_, ?_⟩, bound⟩
                    · rw [outputEq]
                      change RepresentsList arena (remaining.toArray.toList ++ addRefs) (rest ++ addends)
                      simpa only [List.toList_toArray] using represented_append restRep addRep
                    · intro value
                      obtain ⟨sameRest, sameRep, balance⟩ :=
                        NativeCoreUnsignedCancellation.run_value_balance others requested removed value
                      have same := represented_unique restRep sameRep
                      subst sameRest
                      simp only [numerical, addConstant, reduced, List.map_append, List.sum_append, subAmount]
                      have fits : minus.constant.toNat ≤ pool.constant.toNat := canSubtract
                      omega

private theorem represented_usub (held : Represents arena ref term)
    (read : arena[ref]? = some (.node .usub [numerator, denominator, proofRef])) :
    ∃ a b p, term = .usub a b p ∧ Represents arena numerator a ∧ Represents arena denominator b := by
  cases held with
  | var lookup =>
      rw [read] at lookup
      cases lookup
  | node lookup _ children =>
      rw [read] at lookup
      cases lookup
      cases children with
      | cons left rest =>
          cases rest with
          | cons right rest =>
              cases rest with
              | cons proof rest =>
                  cases rest
                  exact ⟨_, _, _, rfl, left, right⟩

structure ScanRewrite (arena : Arena) (pool after : Pool) (terms : List Term) : Prop where
  selected : ∃ before afterTerms a b p,
    terms = before ++ .usub a b p :: afterTerms ∧ Rewrite arena pool after a b (before ++ afterTerms)

theorem scan_refines
    (preceding : RepresentsList arena earlier.reverse earlierTerms)
    (remaining : RepresentsList arena refs terms)
    (accumulated : pool.constant.toNat ≤ initial * maxLiteral)
    (inBudget : initial ≤ limit) (ceiling : limit ≤ 1000000)
    (ran : scan env runtime arena limit depth pool earlier refs initial = (.ok (some after), spent)) :
    ScanRewrite arena pool after (earlierTerms ++ terms) ∧ after.constant.toNat ≤ spent * maxLiteral := by
  induction refs generalizing earlier earlierTerms terms initial with
  | nil => cases ran
  | cons ref rest ih =>
      cases remaining with
      | cons termRep restRep =>
          have followed := represented_append preceding (.cons termRep .nil)
          rw [← List.reverse_cons] at followed
          simp only [scan] at ran
          split at ran
          · rename_i numerator denominator proofRef read
            rcases attempted : attempt env runtime arena limit depth (earlier.reverse ++ rest)
              numerator denominator pool initial with ⟨answer, checked⟩
            cases answer with
            | error reason =>
                simp only [attempted] at ran
                cases ran
            | ok found =>
                cases found with
                | none =>
                    simp only [attempted] at ran
                    have bounded := attempt_bounds (env := env) (runtime := runtime) (arena := arena)
                      (depth := depth) (others := earlier.reverse ++ rest)
                      (numerator := numerator) (denominator := denominator) (pool := pool) inBudget
                    rw [attempted] at bounded
                    have advanced := bounded.2.2 none rfl
                    obtain ⟨⟨head, tail, a, b, p, located, rewritten⟩, bound⟩ :=
                      ih followed restRep (Nat.le_trans accumulated (Nat.mul_le_mul_right _ bounded.1)) advanced ran
                    exact ⟨⟨head, tail, a, b, p, by simpa only [List.append_assoc, List.singleton_append] using located,
                      rewritten⟩, bound⟩
                | some result =>
                    simp only [attempted, Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at ran
                    obtain ⟨rfl, rfl⟩ := ran
                    obtain ⟨a, b, p, rfl, left, right⟩ := represented_usub termRep read
                    obtain ⟨rewritten, bound⟩ :=
                      attempt_refines left right (represented_append preceding restRep) accumulated ceiling attempted
                    exact ⟨⟨_, _, a, b, p, rfl, rewritten⟩, bound⟩
          · obtain ⟨⟨head, tail, a, b, p, located, rewritten⟩, bound⟩ :=
              ih followed restRep accumulated inBudget ran
            exact ⟨⟨head, tail, a, b, p, by simpa only [List.append_assoc, List.singleton_append] using located,
              rewritten⟩, bound⟩

inductive Rewrites (arena : Arena) : Pool → List Term → Pool → Nat → Prop where
  | done : Rewrites arena pool terms pool 0
  | step : ScanRewrite arena pool middle terms →
      RepresentsList arena middle.atoms.toList nextTerms →
      Rewrites arena middle nextTerms after count →
      Rewrites arena pool terms after (count+1)

private theorem runRounds_refines (represented : RepresentsList arena pool.atoms.toList terms)
    (accumulated : pool.constant.toNat ≤ initial * maxLiteral) (inBudget : initial ≤ limit)
    (ceiling : limit ≤ 1000000)
    (ran : runRounds env runtime arena limit depth n pool initial = (.ok (after, count), spent)) :
    Rewrites arena pool terms after count ∧ after.constant.toNat ≤ spent * maxLiteral ∧
      ∃ resultTerms, RepresentsList arena after.atoms.toList resultTerms := by
  induction n generalizing pool terms initial after count spent with
  | zero =>
      cases ran
      exact ⟨.done, accumulated, _, represented⟩
  | succ n ih =>
      simp only [runRounds] at ran
      have steps := scan_bounds (env := env) (runtime := runtime) (arena := arena)
        (depth := depth) (pool := pool) (earlier := []) (refs := pool.atoms.toList) inBudget
      rcases inspected : scan env runtime arena limit depth pool [] pool.atoms.toList initial with ⟨answer, checked⟩
      rw [inspected] at steps
      cases answer with
      | error reason =>
          simp only [inspected] at ran
          cases ran
      | ok found =>
          have within := steps.2.2 found rfl
          cases found with
          | none =>
              simp only [inspected, Prod.mk.injEq, Except.ok.injEq] at ran
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ran
              exact ⟨.done, Nat.le_trans accumulated (Nat.mul_le_mul_right _ steps.1), _, represented⟩
          | some middle =>
              simp only [inspected] at ran
              have hit := scan_refines (earlier := []) .nil represented accumulated inBudget ceiling inspected
              obtain ⟨rewritten, bound⟩ := hit
              have related : ScanRewrite arena pool middle terms := rewritten
              obtain ⟨_, _, _, _, _, _, values⟩ := related.selected
              obtain ⟨_, _, nextTerms, _, _, _, _, nextRep, _⟩ := values.values
              rcases rest : runRounds env runtime arena limit depth n middle checked with ⟨answer, ticks⟩
              cases answer with
              | error reason =>
                  simp only [rest, Except.map] at ran
                  cases ran
              | ok remaining =>
                  obtain ⟨last, priorCount⟩ := remaining
                  simp only [rest, Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := ran
                  obtain ⟨tail, newBound, final⟩ := ih nextRep bound within rest
                  exact ⟨.step related nextRep tail, newBound, final⟩

/-- Every completed production round has a corresponding retained-syntax
rewrite. All successful rounds preserve representation and the U128 bound. -/
theorem rounds_refines (represented : RepresentsList arena pool.atoms.toList terms)
    (accumulated : pool.constant.toNat ≤ initial * maxLiteral) (inBudget : initial ≤ limit)
    (ceiling : limit ≤ 1000000)
    (ran : rounds env runtime arena limit depth pool initial = (.ok (after, count), spent)) :
    Rewrites arena pool terms after count ∧ after.constant.toNat ≤ spent * maxLiteral ∧
      ∃ resultTerms, RepresentsList arena after.atoms.toList resultTerms := by
  unfold rounds at ran
  split at ran
  · exact runRounds_refines represented accumulated inBudget ceiling ran
  · cases ran
    exact ⟨.done, accumulated, _, represented⟩

/-- Removing z exposes the nested subtraction. The next scan removes y,
and reducing the budget by one rejects the numerator's first unpaid tick. -/
theorem nested_subtractions_share_counter :
    let arena : Arena := #[.var 0, .var 1, .var 2, .node (.natural 0) [],
      .node .usub [0, 1, 3], .node .usub [4, 2, 3]]
    let pool : Pool := { atoms := #[5, 2, 1] }
    rounds Environment.empty false arena 10 8 pool 0 = (.ok ({ atoms := #[0] }, 2), 10) ∧
    rounds Environment.empty false arena 9 8 pool 0 = (.error (.stepLimit 0), 10) := by
  constructor <;> cbv

end Jihoo.NativeKernel.NativeCoreUnsignedSumRounds
