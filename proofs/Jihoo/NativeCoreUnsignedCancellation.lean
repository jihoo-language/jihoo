import Jihoo.NativeCoreIdentical

/-! Core.without copies the pool, finds each requested occurrence by live
identity, and charges every entry shifted after removing a match. Both
unsigned sum and subtraction use this same cancellation operation. -/
namespace Jihoo.NativeKernel.NativeCoreUnsignedCancellation

open NativeArena NativeCoreIdentical
open NativeCoreCompare (Shape project)

abbrev Outcome (α : Type) := Except Error α × Nat

def tick (arena : Arena) (limit depth steps ref : Nat) : Outcome Unit :=
  let next := steps + 1
  if limit < next then (.error (.stepLimit ref), next)
  else if depth = 0 then (.error (.depthLimit ref), next)
  else if arena.size ≤ ref then (.error (.invalidReference ref), next)
  else (.ok (), next)

private def charge (arena : Arena) (limit depth : Nat) : Nat → List Nat → Outcome Unit
  | steps, [] => (.ok (), steps)
  | steps, ref :: rest =>
      match tick arena limit depth steps ref with
      | (.error reason, spent) => (.error reason, spent)
      | (.ok (), spent) => charge arena limit depth spent rest

private def removeFirst (arena : Arena) (limit depth item : Nat) :
    Nat → List Nat → Outcome (Option (List Nat))
  | steps, [] => (.ok none, steps)
  | steps, ref :: rest =>
      match runArena arena limit depth steps ref item with
      | (.error reason, spent) => (.error reason, spent)
      | (.ok true, spent) =>
          let shifted := charge arena limit depth spent rest
          (shifted.1.map (fun _ => some rest), shifted.2)
      | (.ok false, spent) =>
          let suffix := removeFirst arena limit depth item spent rest
          (suffix.1.map (Option.map (ref :: ·)), suffix.2)

private def removeItems (arena : Arena) (limit depth : Nat) :
    List Nat → Nat → List Nat → Outcome (Option (List Nat))
  | [], steps, pool => (.ok (some pool), steps)
  | item :: rest, steps, pool =>
      match removeFirst arena limit depth item steps pool with
      | (.error reason, spent) => (.error reason, spent)
      | (.ok none, spent) => (.ok none, spent)
      | (.ok (some remainder), spent) => removeItems arena limit depth rest spent remainder

def run (arena : Arena) (limit depth initial : Nat) (pool items : List Nat) :
    Outcome (Option (List Nat)) :=
  match charge arena limit depth initial pool with
  | (.error reason, spent) => (.error reason, spent)
  | (.ok (), spent) => removeItems arena limit depth items spent pool

private def Within (initial limit : Nat) (outcome : Outcome α) : Prop :=
  initial ≤ outcome.2 ∧ outcome.2 ≤ limit + 1 ∧
    ∀ result, outcome.1 = .ok result → outcome.2 ≤ limit

private theorem Within.rebase (earlier : initial ≤ started) (bounded : Within started limit outcome) :
    Within initial limit outcome :=
  ⟨Nat.le_trans earlier bounded.1, bounded.2⟩

private theorem Within.map {outcome : Outcome α} (bounded : Within initial limit outcome) (f : α → β) :
    Within initial limit (outcome.1.map f, outcome.2) := by
  obtain ⟨answer, steps⟩ := outcome
  refine ⟨bounded.1, bounded.2.1, ?_⟩
  intro _ finished
  cases answer with
  | error => cases finished
  | ok result => exact bounded.2.2 result rfl

private theorem within_ok {result : α} (allowed : steps ≤ limit) : Within steps limit (.ok result, steps) :=
  ⟨Nat.le_refl _, Nat.le_trans allowed (Nat.le_succ _), fun _ _ => allowed⟩

private theorem within_error {α : Type} (earlier : initial ≤ spent) (bounded : spent ≤ limit + 1) :
    Within (α := α) initial limit (.error reason, spent) :=
  ⟨earlier, bounded, by intro _ failed; cases failed⟩

private theorem charge_bounds (within : initial ≤ limit) :
    Within initial limit (charge arena limit depth initial refs) := by
  induction refs generalizing initial with
  | nil => exact within_ok within
  | cons ref rest ih =>
      by_cases over : limit < initial + 1
      · simp only [charge, tick, over, ite_true]
        exact within_error (Nat.le_succ _) (Nat.succ_le_succ within)
      have next : initial + 1 ≤ limit := Nat.le_of_not_gt over
      by_cases zero : depth = 0
      · simp only [charge, tick, over, zero, ite_false, ite_true]
        exact within_error (Nat.le_succ _) (Nat.le_trans next (Nat.le_succ _))
      by_cases invalid : arena.size ≤ ref
      · simp only [charge, tick, over, zero, invalid, ite_false, ite_true]
        exact within_error (Nat.le_succ _) (Nat.le_trans next (Nat.le_succ _))
      · simp only [charge, tick, over, zero, invalid, ite_false]
        exact Within.rebase (Nat.le_succ _) (ih next)

private theorem removeFirst_bounds (within : initial ≤ limit) :
    Within initial limit (removeFirst arena limit depth item initial refs) := by
  induction refs generalizing initial with
  | nil => exact within_ok within
  | cons ref rest ih =>
      have compared : Within initial limit (runArena arena limit depth initial ref item) :=
        runArena_step_bounds within
      rcases matched : runArena arena limit depth initial ref item with ⟨answer, spent⟩
      rw [matched] at compared
      cases answer with
      | error reason =>
          simp only [removeFirst, matched]
          exact within_error compared.1 compared.2.1
      | ok same =>
          have room := compared.2.2 same rfl
          cases same
          · simp only [removeFirst, matched]
            exact Within.rebase compared.1 (Within.map (ih room) _)
          · simp only [removeFirst, matched]
            exact Within.rebase compared.1 (Within.map (charge_bounds (arena := arena) (depth := depth)
              (refs := rest) room) _)

private theorem removeItems_bounds (within : initial ≤ limit) :
    Within initial limit (removeItems arena limit depth items initial pool) := by
  induction items generalizing initial pool with
  | nil => exact within_ok within
  | cons item rest ih =>
      have searched : Within initial limit (removeFirst arena limit depth item initial pool) :=
        removeFirst_bounds within
      rcases removed : removeFirst arena limit depth item initial pool with ⟨answer, spent⟩
      rw [removed] at searched
      cases answer with
      | error reason =>
          simp only [removeItems, removed]
          exact within_error searched.1 searched.2.1
      | ok found =>
          have room := searched.2.2 found rfl
          cases found
          · simp only [removeItems, removed]
            exact Within.rebase searched.1 (within_ok room)
          · simp only [removeItems, removed]
            exact Within.rebase searched.1 (ih room)

/-- Copying, scanning, and shifting share the same stopping counter. With
an in-budget entry, only the first rejecting tick can exceed the limit. -/
theorem run_step_bounds (within : initial ≤ limit) :
    let outcome := run arena limit depth initial pool items
    initial ≤ outcome.2 ∧ outcome.2 ≤ limit + 1 ∧
      ∀ result, outcome.1 = .ok result → outcome.2 ≤ limit := by
  have copied : Within initial limit (charge arena limit depth initial pool) := charge_bounds within
  rcases copyResult : charge arena limit depth initial pool with ⟨answer, spent⟩
  rw [copyResult] at copied
  cases answer with
  | error reason =>
      simp only [run, copyResult]
      exact within_error copied.1 copied.2.1
  | ok copiedValue =>
      cases copiedValue
      simp only [run, copyResult]
      exact Within.rebase copied.1 (removeItems_bounds (copied.2.2 () rfl))

/-- Remove the first matching shape, or report that no occurrence exists. -/
inductive RemoveFirst (item : Shape) : List Shape → Option (List Shape) → Prop where
  | missing : RemoveFirst item [] none
  | hit : RemoveFirst item (item :: rest) (some rest)
  | skip : head ≠ item → RemoveFirst item rest result →
      RemoveFirst item (head :: rest) (result.map (head :: ·))

/-- Process requests in order and stop as soon as a match is missing. -/
inductive RemoveItems : List Shape → List Shape → Option (List Shape) → Prop where
  | finished : RemoveItems pool [] (some pool)
  | missing : RemoveFirst item pool none → RemoveItems pool (item :: rest) none
  | next : RemoveFirst item pool (some remainder) → RemoveItems remainder rest result →
      RemoveItems pool (item :: rest) result

def RepresentsResult (arena : Arena) (refs : Option (List Nat))
    (shapes : Option (List Shape)) : Prop :=
  match refs, shapes with
  | none, none => True
  | some refs, some shapes => ∃ terms, RepresentsList arena refs terms ∧ shapes = terms.map project
  | _, _ => False

private theorem RepresentsResult.cons (represented : RepresentsResult arena refs shapes)
    (head : Represents arena ref term) :
    RepresentsResult arena (refs.map (ref :: ·)) (shapes.map (project term :: ·)) := by
  cases refs <;> cases shapes
  · trivial
  · exact False.elim represented
  · exact False.elim represented
  · obtain ⟨terms, suffix, rfl⟩ := represented
    exact ⟨term :: terms, .cons head suffix, rfl⟩

private theorem removeFirst_refines (pool : RepresentsList arena refs terms)
    (item : Represents arena needle target)
    (ran : removeFirst arena limit depth needle initial refs = (.ok result, spent)) :
    ∃ shapes, RemoveFirst (project target) (terms.map project) shapes ∧
      RepresentsResult arena result shapes := by
  induction refs generalizing terms initial result spent with
  | nil =>
      cases pool
      cases ran
      exact ⟨none, .missing, trivial⟩
  | cons ref refs ih =>
    cases pool with
    | @cons _ term _ terms head rest =>
      unfold removeFirst at ran
      rcases matched : runArena arena limit depth initial ref needle with ⟨answer, afterMatch⟩
      cases answer with
      | error reason => simp [matched] at ran
      | ok same =>
          have equivalent := runArena_refines head item matched
          cases same with
          | false =>
              have distinct : project term ≠ project target :=
                fun equal => Bool.false_ne_true (equivalent.mpr equal)
              rcases removed : removeFirst arena limit depth needle afterMatch refs with ⟨answer, afterRemove⟩
              cases answer with
              | error reason => simp [matched, removed, Except.map] at ran
              | ok found =>
                  simp only [matched, removed, Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
                  obtain ⟨rfl, rfl⟩ := ran
                  obtain ⟨shapes, reflected, represented⟩ := ih rest removed
                  exact ⟨_, .skip distinct reflected, represented.cons head⟩
          | true =>
              have equal := equivalent.mp rfl
              rcases shifted : charge arena limit depth afterMatch refs with ⟨answer, afterShift⟩
              cases answer with
              | error reason => simp [matched, shifted, Except.map] at ran
              | ok _ =>
                  simp only [matched, shifted, Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
                  obtain ⟨rfl, rfl⟩ := ran
                  refine ⟨some (terms.map project), ?_, ⟨terms, rest, rfl⟩⟩
                  simp only [List.map_cons, equal]
                  exact .hit

private theorem removeItems_refines (needles : RepresentsList arena items requests)
    (pool : RepresentsList arena refs terms)
    (ran : removeItems arena limit depth items initial refs = (.ok result, spent)) :
    ∃ shapes, RemoveItems (terms.map project) (requests.map project) shapes ∧
      RepresentsResult arena result shapes := by
  induction items generalizing requests initial refs terms result spent with
  | nil =>
      cases needles
      cases ran
      exact ⟨some (terms.map project), .finished, ⟨terms, pool, rfl⟩⟩
  | cons ref items ih =>
    cases needles with
    | @cons _ term _ requests head rest =>
      unfold removeItems at ran
      rcases searched : removeFirst arena limit depth ref initial refs with ⟨answer, afterSearch⟩
      cases answer with
      | error reason => simp [searched] at ran
      | ok found =>
          obtain ⟨shapes, reflected, represented⟩ := removeFirst_refines pool head searched
          cases found <;> cases shapes
          · simp only [searched, Prod.mk.injEq, Except.ok.injEq] at ran
            obtain ⟨rfl, rfl⟩ := ran
            exact ⟨none, .missing reflected, trivial⟩
          · exact False.elim represented
          · exact False.elim represented
          · obtain ⟨remaining, suffix, rfl⟩ := represented
            simp only [searched] at ran
            obtain ⟨output, replayed, representation⟩ := ih rest suffix ran
            exact ⟨output, .next reflected replayed, representation⟩

/-- Every completed cancellation call agrees with independent first-match
removal on the represented comparison shapes. -/
theorem run_refines (pool : RepresentsList arena refs terms)
    (items : RepresentsList arena needles requests)
    (ran : run arena limit depth initial refs needles = (.ok result, spent)) :
    ∃ shapes, RemoveItems (terms.map project) (requests.map project) shapes ∧
      RepresentsResult arena result shapes := by
  unfold run at ran
  rcases copied : charge arena limit depth initial refs with ⟨answer, afterCopy⟩
  cases answer with
  | error reason => simp [copied] at ran
  | ok copiedValue =>
      cases copiedValue
      simp only [copied] at ran
      exact removeItems_refines items pool ran

theorem RemoveFirst.perm (removed : RemoveFirst item pool (some remainder)) :
    (item :: remainder).Perm pool := by
  generalize output : some remainder = output at removed
  induction removed generalizing remainder with
  | missing => cases output
  | hit =>
      cases output
      exact .refl _
  | @skip head rest result distinct removed ih =>
      cases result with
      | none => cases output
      | some suffix =>
          cases output
          exact (List.Perm.swap head item suffix).trans ((ih rfl).cons head)

/-- The remaining pool and exactly one occurrence per request account for
every initial occurrence, including shared references and duplicates. -/
theorem RemoveItems.perm (removed : RemoveItems pool items (some remainder)) :
    (items ++ remainder).Perm pool := by
  generalize output : some remainder = output at removed
  induction removed generalizing remainder with
  | finished =>
      cases output
      exact .refl _
  | missing => cases output
  | next first _ ih =>
      exact ((ih output).cons _).trans first.perm

private theorem perm_total (same : List.Perm left right) (value : Shape → Nat) :
    (left.map value).sum = (right.map value).sum := by
  induction same with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [Nat.add_left_comm]
  | trans _ _ first second => exact first.trans second

/-- Successful live cancellation subtracts exactly the requested value
under any assignment constant on the compiler's comparison shapes. -/
theorem run_value_balance (pool : RepresentsList arena refs terms)
    (requests : RepresentsList arena items needles)
    (ran : run arena limit depth initial refs items = (.ok (some residual), spent))
    (value : Shape → Nat) :
    ∃ remainder, RepresentsList arena residual remainder ∧
      (terms.map (value ∘ project)).sum =
        (needles.map (value ∘ project)).sum + (remainder.map (value ∘ project)).sum := by
  obtain ⟨shapes, removed, output⟩ := run_refines pool requests ran
  cases shapes with
  | none => exact False.elim output
  | some shapes =>
      obtain ⟨rest, represented, rfl⟩ := output
      refine ⟨rest, represented, ?_⟩
      simpa only [List.map_append, List.sum_append, List.map_map] using
        (perm_total (RemoveItems.perm removed) value).symm

/-- The first removal charges both shifted entries. The second must compare
the earlier nonmatch before it can consume the remaining duplicate. -/
theorem duplicate_and_shift_limit :
    let arena : Arena := #[.var 0, .var 1]
    run arena 8 1 0 [0, 1, 0] [0, 0] = (.ok (some [1]), 8) ∧
    run arena 5 1 0 [0, 1, 0] [0, 0] = (.error (.stepLimit 0), 6) := by
  exact ⟨rfl, rfl⟩

end Jihoo.NativeKernel.NativeCoreUnsignedCancellation
