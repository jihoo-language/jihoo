import Jihoo.NativeCoreCompareWire

/-! The finite execution of Core.identical on observed version-6 rows. This
traversal has a different budget path from Core.compare. It checks a vector's
length at entry, and even equal references take the complete visited path. -/
namespace Jihoo.NativeKernel.NativeCoreIdentical

open NativeArena NativeCoreGraph NativeCoreCompare GraphCertificates.Canonical

inductive Error where
  | stepLimit (reference : Nat)
  | depthLimit (reference : Nat)
  | invalidReference (reference : Nat)
  deriving Repr, DecidableEq

abbrev Result := Except Error Bool × Nat

private def finished (same : Bool) (steps : Nat) : Result := (.ok same, steps)
private def failed (reason : Error) (steps : Nat) : Result := (.error reason, steps)

private def afterTrue (current : Result) (next : Nat → Result) : Result :=
  match current with
  | (.ok true, steps) => next steps
  | other => other

abbrev CompareChildren := Nat → Nat → Nat → Result

private def identicalList (step : CompareChildren) : Nat → List Nat → List Nat → Result
  | steps, [], [] => finished true steps
  | steps, x :: xs, y :: ys =>
      afterTrue (step steps x y) (fun next => identicalList step next xs ys)
  | steps, _, _ => finished false steps

private def identicalVector (step : CompareChildren) (steps : Nat) (xs ys : List Nat) : Result :=
  if xs.length = ys.length then identicalList step steps xs ys else finished false steps

/-- Ind, Con and Elements enter their vector directly. Elim, Case and View
first compare the motive, then check the middle vector, then compare its
elements and the final scrutinee. -/
inductive ChildOrder where
  | ordered
  | vector
  | motiveVector
  deriving DecidableEq

def childOrder : Nat → ChildOrder
  | 11 | 12 | 38 => .vector
  | 13 | 32 | 46 => .motiveVector
  | _ => .ordered

theorem childOrder_schema (op : Op) :
    childOrder (ACU.Canonical.rank op) =
      match op with
      | .ind .. | .con .. | .elements .. => .vector
      | .elim .. | .caseOf .. | .view .. => .motiveVector
      | _ => .ordered := by
  cases op <;> rfl

def runChildren (step : CompareChildren) (rank steps : Nat) (xs ys : List Nat) : Result :=
  match childOrder rank with
  | .ordered => identicalList step steps xs ys
  | .vector => identicalVector step steps xs ys
  | .motiveVector =>
      match xs, ys with
      | x :: xs, y :: ys =>
          afterTrue (step steps x y) (fun next => identicalVector step next xs ys)
      | _, _ => identicalList step steps xs ys

/-- Exact tick order at each entry to Core.identical, parameterized by the
absolute checking step limit. The right lookup failure is only reachable
outside checked graph inputs. -/
def run (words : List NodeWords) (limit : Nat) : Nat → Nat → Nat → Nat → Result
  | 0, steps, a, _ =>
      if limit < steps + 1 then failed (.stepLimit a) (steps + 1)
      else failed (.depthLimit a) (steps + 1)
  | depth + 1, steps, a, b =>
      let steps := steps + 1
      if limit < steps then failed (.stepLimit a) steps else
      match words[a]? with
      | none => failed (.invalidReference a) steps
      | some left =>
          match wireView left with
          | .strict next => run words limit depth steps next b
          | .plain x xs =>
              match words[b]? with
              | none => failed (.invalidReference b) steps
              | some right =>
                  match wireView right with
                  | .strict next => run words limit depth steps a next
                  | .plain y ys =>
                      if x = y then runChildren (run words limit depth) x.1 steps xs ys
                      else finished false steps

theorem step_limit_first (exceeded : limit < steps + 1) :
    run words limit depth steps a b = (.error (.stepLimit a), steps + 1) := by
  cases depth <;> simp [run, exceeded, failed]

theorem depth_limit (available : steps + 1 ≤ limit) :
    run words limit 0 steps a b = (.error (.depthLimit a), steps + 1) := by
  simp [run, Nat.not_lt.mpr available, failed]

theorem vector_mismatch (order : childOrder rank = .vector) (different : xs.length ≠ ys.length) :
    runChildren step rank steps xs ys = (.ok false, steps) := by
  simp [runChildren, order, identicalVector, different, finished]

theorem motive_vector_mismatch (order : childOrder rank = .motiveVector)
    (different : xs.length ≠ ys.length) (motive : step steps x y = (.ok true, next)) :
    runChildren step rank steps (x :: xs) (y :: ys) = (.ok false, next) := by
  simp [runChildren, order, afterTrue, motive, identicalVector, different, finished]

private theorem afterTrue_matches {P Q : Prop}
    {current : Result} {next : Nat → Result}
    (firstSpec : ∀ value steps, current = (.ok value, steps) → (value = true ↔ P))
    (nextSpec : ∀ initial value steps, next initial = (.ok value, steps) → (value = true ↔ Q))
    (computed : afterTrue current next = (.ok result, steps)) :
    result = true ↔ P ∧ Q := by
  obtain ⟨current, counter⟩ := current
  cases current with
  | error reason => simp [afterTrue] at computed
  | ok same =>
      cases same with
      | false =>
          have rejected := firstSpec false counter rfl
          simp only [afterTrue, Prod.mk.injEq, Except.ok.injEq] at computed
          obtain ⟨rfl, rfl⟩ := computed
          simp [← rejected]
      | true =>
          have accepted := (firstSpec true counter rfl).mp rfl
          simp only [afterTrue] at computed
          simpa only [accepted, true_and] using nextSpec counter result steps computed

private theorem represented_length (children : RepresentsList arena refs terms) :
    refs.length = terms.length := by
  induction children using RepresentsList.rec (motive_1 := fun _ _ _ => True) with
  | var | node => trivial
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

private def StepMatches (arena : Arena) (step : CompareChildren) : Prop :=
  ∀ {initial a b first second result steps},
    Represents arena a first → Represents arena b second →
    step initial a b = (.ok result, steps) →
    (result = true ↔ project first = project second)

private theorem identicalList_matches {step : CompareChildren} (stepSpec : StepMatches arena step)
    (left : RepresentsList arena xs firsts) (right : RepresentsList arena ys seconds)
    (computed : identicalList step initial xs ys = (.ok result, steps)) :
    result = true ↔ firsts.map project = seconds.map project := by
  induction left using RepresentsList.rec (motive_1 := fun _ _ _ => True)
      generalizing initial ys seconds result steps with
  | var | node => trivial
  | nil =>
      cases right <;> cases computed <;> simp
  | cons first rest _ ih =>
      cases right with
      | nil => cases computed; simp
      | cons second tail =>
          have compared := afterTrue_matches
            (fun _ _ computed => stepSpec first second computed)
            (fun _ _ _ computed => ih tail computed) computed
          simpa only [List.map_cons, List.cons.injEq] using compared

private theorem identicalVector_matches {step : CompareChildren} (stepSpec : StepMatches arena step)
    (left : RepresentsList arena xs firsts) (right : RepresentsList arena ys seconds)
    (computed : identicalVector step initial xs ys = (.ok result, steps)) :
    result = true ↔ firsts.map project = seconds.map project := by
  unfold identicalVector at computed
  split at computed
  · exact identicalList_matches stepSpec left right computed
  · rename_i different
    have distinct : firsts.map project ≠ seconds.map project := by
      intro same
      apply different
      rw [represented_length left, represented_length right]
      simpa only [List.length_map] using congrArg List.length same
    cases computed
    simp [distinct]

private theorem runChildren_matches {step : CompareChildren} (stepSpec : StepMatches arena step)
    (left : RepresentsList arena xs firsts) (right : RepresentsList arena ys seconds)
    (computed : runChildren step rank initial xs ys = (.ok result, steps)) :
    result = true ↔ firsts.map project = seconds.map project := by
  unfold runChildren at computed
  cases order : childOrder rank with
  | ordered => exact identicalList_matches stepSpec left right (by simpa only [order] using computed)
  | vector => exact identicalVector_matches stepSpec left right (by simpa only [order] using computed)
  | motiveVector =>
      simp only [order] at computed
      cases left with
      | nil => exact identicalList_matches stepSpec .nil right computed
      | cons first rest =>
          cases right with
          | nil => exact identicalList_matches stepSpec (.cons first rest) .nil computed
          | cons second tail =>
              have compared := afterTrue_matches
                (fun _ _ computed => stepSpec first second computed)
                (fun _ _ _ computed => identicalVector_matches stepSpec rest tail computed) computed
              simpa only [List.map_cons, List.cons.injEq] using compared

private theorem run_matches
    (aligned : words.mapM NodeWords.toNode = some arena.toList)
    (left : Represents arena a first) (right : Represents arena b second)
    (computed : run words limit depth initial a b = (.ok result, steps)) :
    result = true ↔ project first = project second := by
  induction depth generalizing a b first second initial result steps with
  | zero =>
      simp only [run] at computed
      split at computed <;> cases computed
  | succ depth ih =>
      by_cases exceeded : limit < initial + 1
      · simp [run, exceeded, failed] at computed
      · obtain ⟨leftWord, leftFound, leftView⟩ := wire_matches aligned left
        simp only [run, ite_eq_right exceeded, leftFound] at computed
        cases shapeLeft : wireView leftWord with
        | strict next =>
            rw [shapeLeft] at leftView computed
            obtain ⟨child, represented, projected⟩ := leftView
            rw [projected]
            exact ih represented right computed
        | plain x xs =>
            rw [shapeLeft] at leftView computed
            obtain ⟨childrenLeft, kidsLeft, projectedLeft⟩ := leftView
            obtain ⟨rightWord, rightFound, rightView⟩ := wire_matches aligned right
            simp only [rightFound] at computed
            cases shapeRight : wireView rightWord with
            | strict next =>
                rw [shapeRight] at rightView computed
                obtain ⟨child, represented, projected⟩ := rightView
                rw [projected]
                exact ih left represented computed
            | plain y ys =>
                rw [shapeRight] at rightView computed
                obtain ⟨childrenRight, kidsRight, projectedRight⟩ := rightView
                dsimp only at computed
                by_cases header : x = y
                · subst y
                  simp only [ite_true] at computed
                  have childSpec : StepMatches arena (run words limit depth) :=
                    fun left right child => ih left right child
                  have equal := runChildren_matches childSpec kidsLeft kidsRight computed
                  simpa only [projectedLeft, projectedRight, Shape.node.injEq, true_and] using equal
                · rw [ite_eq_right header] at computed
                  cases computed
                  simp [projectedLeft, projectedRight, Shape.node.injEq, header]

/-- Every completed call on a represented version-6 pair returns exactly
structural identity after Strict and proof-slot projection. -/
theorem run_refines (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ tail) =
      some (snapshot, rest))
    (left : Represents snapshot.arena a first) (right : Represents snapshot.arena b second)
    (computed : run words limit depth initial a b = (.ok result, steps)) :
    result = true ↔ project first = project second := by
  rw [parseObservedProgram _ _ _ fits] at parsed
  cases aligned : words.mapM NodeWords.toNode with
  | none => simp [aligned] at parsed
  | some nodes =>
      simp only [aligned, Option.map_some, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨rfl, rfl⟩ := parsed
      exact run_matches (by simpa using aligned) left right computed

theorem run_agrees_compare (fits : ∀ word ∈ words, word.fits)
    (parsed : NativeFamilyWire.parseSnapshot (encodeObservedProgram definitions families words ++ tail) =
      some (snapshot, rest))
    (left : Represents snapshot.arena a first) (right : Represents snapshot.arena b second)
    (identified : run words limit depth initial a b = (.ok result, steps))
    (compared : compareGraph words compareDepth work a b = some (order, remaining)) :
    result = true ↔ order = .eq :=
  (run_refines fits parsed left right identified).trans (compareGraph_zero_iff fits parsed left right compared).symm

/-- The Strict wrappers take one tick each, the common sum takes one, and its
two references to the same literal are visited separately. One less tick
rejects at the second visit to that literal. -/
theorem repeated_reference_cost (initial : Nat) :
    let words : List NodeWords := [⟨47, [7], []⟩, ⟨17, [], [0, 0]⟩, ⟨16, [], [0, 1]⟩]
    run words (initial + 5) 4 initial 2 2 = (.ok true, initial + 5) ∧
      run words (initial + 4) 4 initial 2 2 = (.error (.stepLimit 0), initial + 5) := by
  simp [run, wireView, wireRank, wirePayload, wireChildren, childOrder, runChildren, identicalList,
    afterTrue, finished, failed, Nat.add_assoc]


/-- Leading Strict nodes are visited on the left and right separately. -/
inductive LeadingStrict (words : List NodeWords) : Nat → Nat → Nat → Prop where
  | done : LeadingStrict words root 0 root
  | next (found : words[root]? = some word) (strict : wireView word = .strict next)
      (rest : LeadingStrict words next wraps base) : LeadingStrict words root (wraps + 1) base

private theorem LeadingStrict.skipLeft (leading : LeadingStrict words root wraps base)
    (space : initial + wraps ≤ limit) :
    run words limit (depth + wraps) initial root other =
      run words limit depth (initial + wraps) base other := by
  induction leading generalizing depth initial with
  | done => rfl
  | @next root word next wraps base found strict rest ih =>
      have available : ¬limit < initial + 1 := by omega
      have more : initial + 1 + wraps ≤ limit := by omega
      simp only [Nat.add_succ, run, ite_eq_right available, found, strict]
      have equal : initial + (wraps + 1) = (initial + 1) + wraps := by omega
      change run words limit (depth + wraps) (initial + 1) next other =
        run words limit depth (initial + (wraps + 1)) base other
      rw [equal]
      exact ih more

private theorem LeadingStrict.skipRight (leading : LeadingStrict words root wraps base)
    (found : words[left]? = some word) (plain : wireView word = .plain head refs)
    (space : initial + wraps ≤ limit) :
    run words limit (depth + wraps) initial left root =
      run words limit depth (initial + wraps) left base := by
  induction leading generalizing depth initial with
  | done => rfl
  | @next root rightWord next wraps base rightFound strict rest ih =>
      have available : ¬limit < initial + 1 := by omega
      have more : initial + 1 + wraps ≤ limit := by omega
      simp only [Nat.add_succ, run, ite_eq_right available, found, plain, rightFound, strict]
      have equal : initial + (wraps + 1) = (initial + 1) + wraps := by omega
      change run words limit (depth + wraps) (initial + 1) left next =
        run words limit depth (initial + (wraps + 1)) left base
      rw [equal]
      exact ih more

mutual
  /-- Count the two leading Strict walks and then the constructor and every
  retained child occurrence. The index gives sufficient recursion depth. -/
  inductive SelfCost (words : List NodeWords) : Nat → Nat → Nat → Prop where
    | node (leading : LeadingStrict words root wraps base)
        (found : words[base]? = some word) (plain : wireView word = .plain head refs)
        (children : SelfCosts words refs childDepth childTicks) :
        SelfCost words root (childDepth + 1 + (wraps + wraps)) (wraps + wraps + 1 + childTicks)

  inductive SelfCosts (words : List NodeWords) : List Nat → Nat → Nat → Prop where
    | nil : SelfCosts words [] 0 0
    | cons (head : SelfCost words ref headDepth headTicks) (rest : SelfCosts words refs tailDepth tailTicks) :
        SelfCosts words (ref :: refs) (max headDepth tailDepth) (headTicks + tailTicks)
end

private theorem runChildren_same (step : CompareChildren) (rank initial : Nat) (refs : List Nat) :
    runChildren step rank initial refs refs = identicalList step initial refs refs := by
  unfold runChildren
  cases childOrder rank <;> cases refs <;>
    simp [identicalVector, identicalList]

/-- For any graph with a checked self-cost derivation, the model spends
exactly that many ticks under sufficient depth and an available step budget.
Every occurrence of a shared reference contributes its full cost. -/
theorem SelfCost.execute (cost : SelfCost words root needed ticks)
    (height : needed ≤ depth) (space : initial + ticks ≤ limit) :
    run words limit depth initial root root = (.ok true, initial + ticks) := by
  induction cost using SelfCost.rec
    (motive_2 := fun refs needed ticks _ => ∀ depth initial, needed ≤ depth → initial + ticks ≤ limit →
      identicalList (run words limit depth) initial refs refs = (.ok true, initial + ticks))
      generalizing depth initial with
  | @node root wraps base word head refs childDepth childTicks leading found plain children ih =>
      let ordinaryDepth := depth - (wraps + wraps)
      have rebuild : depth = ordinaryDepth + wraps + wraps := by dsimp [ordinaryDepth]; omega
      have leftSpace : initial + wraps ≤ limit := by omega
      have rightSpace : initial + wraps + wraps ≤ limit := by omega
      have ordinarySpace : ¬limit < initial + wraps + wraps + 1 := by omega
      rw [rebuild, leading.skipLeft leftSpace, leading.skipRight found plain rightSpace]
      have ordinaryEnough : childDepth + 1 ≤ ordinaryDepth := by dsimp [ordinaryDepth]; omega
      cases onDepth : ordinaryDepth with
      | zero => omega
      | succ rest =>
          simp only [run, ite_eq_right ordinarySpace, found, plain, ite_true, runChildren_same]
          have computed := ih rest (initial + wraps + wraps + 1) (by omega) (by omega)
          simpa only [Nat.add_assoc] using computed
  | nil => simp [identicalList, finished]
  | @cons ref headDepth headTicks refs tailDepth tailTicks head rest ihHead ihTail =>
      rename_i depth initial height space
      have headRan := ihHead (depth := depth) (initial := initial) (by omega) (by omega)
      simp only [identicalList, headRan, afterTrue]
      simpa only [Nat.add_assoc] using ihTail depth (initial + headTicks) (by omega) (by omega)

end Jihoo.NativeKernel.NativeCoreIdentical
